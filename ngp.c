/* Copyright (C) 2013  Jonathan Klee, Guillaume Quéré

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

#define _GNU_SOURCE

#include <stdlib.h>
#include <stdio.h>
#include <sys/types.h>
#include <limits.h>
#include <dirent.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <sys/wait.h>
#include <ncurses.h>
#include <menu.h>
#include <signal.h>
#include <libconfig.h>
#include <sys/stat.h>
#include <pthread.h>
#include <ctype.h>
#include <regex.h>

#define CURSOR_UP 	'k'
#define CURSOR_DOWN 	'j'
#define PAGE_UP		'K'
#define PAGE_DOWN	'J'
#define ENTER	 	'p'
#define QUIT	 	'q'

#ifdef LINE_MAX
	#undef LINE_MAX
#endif
#define LINE_MAX	256

#define S_VAR_NOT_USED(x) do{(void)(x);}while(0);

#define synchronized(MUTEX) \
for(mutex = &MUTEX; \
mutex && !pthread_mutex_lock(mutex); \
pthread_mutex_unlock(mutex), mutex = 0)

typedef struct s_entry_t {
	char *data;
	char isfile:1;
} entry_t;

typedef struct s_exclude_list {
	char			path[LINE_MAX];
	struct s_exclude_list	*next;
} exclude_list_t;

typedef struct s_extension_list {
	char			ext[LINE_MAX];
	struct s_extension_list	*next;
} extension_list_t;

typedef struct s_specific_files {
	char			spec[LINE_MAX];
	struct s_specific_files	*next;
} specific_files_t;

typedef struct s_search_t {
	/* screen */
	int index;
	int cursor;

	/* data */
	entry_t *entries;
	unsigned int nbentry;
	unsigned int nb_lines;
	unsigned int size;

	/* thread */
	pthread_mutex_t data_mutex;
	unsigned int status:1;

	/* search */
	char directory[PATH_MAX];
	char pattern[LINE_MAX];
	char options[LINE_MAX];
	unsigned int is_regex:1;
	regex_t *regex;

	/* search in search */
	struct s_search_t *father;
	struct s_search_t *child;
} search_t;

/* attributes specific to mainsearch */
typedef struct s_mainsearch_attr {
	unsigned int raw:1;
	unsigned int follow_symlinks:1;
	unsigned int has_excludes:1;

	exclude_list_t		*firstexcl;
	specific_files_t	*firstspec;
	extension_list_t	*firstext;
} mainsearch_attr_t;

static search_t			mainsearch;
static mainsearch_attr_t	mainsearch_attr;
static search_t			*current;
static pthread_t		pid;

static void usage(void);

/*************************** INIT *********************************************/
static void configuration_init(config_t *cfg)
{
	char *user_name;
	char user_ngprc[PATH_MAX];

	config_init(cfg);

	user_name = getenv("USER");
	snprintf(user_ngprc, PATH_MAX, "/home/%s/%s",
		user_name, ".ngprc");

	if (config_read_file(cfg, user_ngprc))
		return;

	if (!config_read_file(cfg, "/etc/ngprc")) {
		fprintf(stderr, "error in /etc/ngprc\n");
		fprintf(stderr, "Configuration file has not been found\n");
		config_destroy(cfg);
		exit(1);
	}
}

void init_searchstruct(search_t *searchstruct)
{
	searchstruct->index = 0;
	searchstruct->cursor = 0;
	searchstruct->size = 100;
	searchstruct->nbentry = 0;
	searchstruct->nb_lines = 0;
	searchstruct->status = 1;
	searchstruct->is_regex = 0;
	strcpy(searchstruct->directory, "./");
	searchstruct->father = NULL;
	searchstruct->child = NULL;
}

static void ncurses_init()
{
	initscr();
	cbreak();
	noecho();
	keypad(stdscr, TRUE);
	nodelay(stdscr, TRUE);
	start_color();
	use_default_colors();
	init_pair(1, -1, -1);
	init_pair(2, COLOR_YELLOW, -1);
	init_pair(3, COLOR_RED, -1);
	init_pair(4, COLOR_MAGENTA, -1);
	init_pair(5, COLOR_GREEN, -1);
	curs_set(0);
}

void get_config(const char *editor, extension_list_t **curext,
		specific_files_t **curspec)
{
	char *ptr;
	char *buf;
	config_t cfg;
	const char *specific_files;
	const char *extensions;
	specific_files_t	*tmpspec;
	extension_list_t	*tmpext;

	/* grab conf */
	configuration_init(&cfg);
	if (!config_lookup_string(&cfg, "editor", &editor)) {
		fprintf(stderr, "ngprc: no editor string found!\n");
		exit(-1);
	}

	if (!config_lookup_string(&cfg, "files", &specific_files)) {
		fprintf(stderr, "ngprc: no files string found!\n");
		exit(-1);
	}

	/* get specific files names from configuration */
	ptr = strtok_r((char *) specific_files, " ", &buf);
	while (ptr != NULL) {
		tmpspec = malloc(sizeof(specific_files_t));
		if (!mainsearch_attr.firstspec) {
			mainsearch_attr.firstspec = tmpspec;
		} else {
			(*curspec)->next = tmpspec;
		}

		strncpy(tmpspec->spec, ptr, LINE_MAX);
		*curspec = tmpspec;
		ptr = strtok_r(NULL, " ", &buf);
	}

	/* get files extensions from configuration */
	if (!config_lookup_string(&cfg, "extensions", &extensions)) {
		fprintf(stderr, "ngprc: no extensions string found!\n");
		exit(-1);
	}

	ptr = strtok_r((char *) extensions, " ", &buf);
	while (ptr != NULL) {
		tmpext = malloc(sizeof(struct s_extension_list));
		if (!mainsearch_attr.firstext) {
			mainsearch_attr.firstext = tmpext;
		} else {
			(*curext)->next = tmpext;
		}

		strncpy(tmpext->ext, ptr, LINE_MAX);
		*curext = tmpext;
		ptr = strtok_r(NULL, " ", &buf);
	}
}

void get_args(int argc, char *argv[], extension_list_t **curext, exclude_list_t **curexcl)
{
	int opt;
	exclude_list_t		*tmpexcl;
	extension_list_t	*tmpext;

	while ((opt = getopt(argc, argv, "hit:refx:")) != -1) {
		switch (opt) {
		case 'h':
			usage();
			break;
		case 'i':
			strcpy(mainsearch.options, "-i");
			break;
		case 't':
			//FIXME: maybe the LL is empty hehe ...
			tmpext = malloc(sizeof(extension_list_t));
			strncpy(tmpext->ext, optarg, LINE_MAX);
			(*curext)->next = tmpext;
			*curext = tmpext;
			break;
		case 'r':
			mainsearch_attr.raw = 1;
			break;
		case 'e':
			mainsearch.is_regex = 1;
			break;
		case 'f':
			mainsearch_attr.follow_symlinks = 1;
			break;
		case 'x':
			tmpexcl = malloc(sizeof(exclude_list_t));
			if (!mainsearch_attr.firstexcl) {
				mainsearch_attr.has_excludes = 1;
				mainsearch_attr.firstexcl = tmpexcl;
			} else {
				(*curexcl)->next = tmpexcl;
			}

			strncpy(tmpexcl->path, optarg, LINE_MAX);
			if (tmpexcl->path[strlen(tmpexcl->path) - 1] == '/')
				tmpexcl->path[strlen(tmpexcl->path) - 1] = 0;
			*curexcl = tmpexcl;
			break;
		default:
			exit(-1);
			break;
		}
	}
}


/*************************** UTILS ********************************************/
static int is_file(int index)
{
	return current->entries[index].isfile;
}

static int isfile(char *nodename)
{
	struct stat buf;

	stat(nodename, &buf);
	return !S_ISDIR(buf.st_mode);
}

static int is_dir_good(char *dir)
{
	exclude_list_t *curex;

	/* check if directory has been excluded */
	if (mainsearch_attr.has_excludes) {
		curex = mainsearch_attr.firstexcl;
		while (curex) {
			if (!strncmp(curex->path, dir, LINE_MAX)) {
				return 0;
			}
			curex = curex->next;
		}
	}

	/* check if directory shouldn't be browsed at all */
	return  strcmp(dir, ".") != 0 &&
		strcmp(dir, "..") != 0 &&
		strcmp(dir, ".git") != 0 &&
		strcmp(dir, ".svn") != 0 ? 1 : 0;
}

static int is_simlink(char *file_path)
{
	struct stat filestat;

	lstat(file_path, &filestat);
	return S_ISLNK(filestat.st_mode);
}

static int is_specific_file(const char *name)
{
	char *name_begins;
	specific_files_t *curspec;

	curspec = mainsearch_attr.firstspec;
	while (curspec) {
		name_begins = (strrchr(name, '/') != NULL) ? strrchr(name, '/') + 1 : (char *) name;
		if (!strncmp(name_begins, curspec->spec, LINE_MAX))
			return 1;
		curspec = curspec->next;
	}
	return 0;
}

static char * remove_double_appearance(char *initial, char c, char *final)
{
	int i, j;
	int len = strlen(initial);

	for (i = 0, j = 0; i < len; j++ ) {
		if (initial[i] != c) {
			final[j] = initial[i];
			i++;
		} else {
			final[j] = initial[i];
			if (initial[i + 1] == c) {
				i = i + 2;
			} else {
				i++;
			}
		}
	}
	final[j] = '\0';

	return final;
}

static char * extract_line_number(char *line)
{
	char *token;
	char *buffer;
	token = strtok_r(line, " :", &buffer);
	return token;
}

static void usage(void)
{
	fprintf(stderr, "usage: ngp [options]... pattern [directory/file]\n\n");
	fprintf(stderr, "options:\n");
	fprintf(stderr, " -i : ignore case distinctions in pattern\n");
	fprintf(stderr, " -r : raw mode\n");
	fprintf(stderr, " -t type : look for a file extension only\n");
	fprintf(stderr, " -e : pattern is a regexp\n");
	fprintf(stderr, " -x folder : exclude directory from search\n");
	fprintf(stderr, " -f : follow symlinks (default doesn't)\n");
	exit(-1);
}

int find_file(int index)
{
	while (!is_file(index))
		index--;

	return index;
}

static void open_entry(int index, const char *editor, const char *pattern)
{
	char command[PATH_MAX];
	char filtered_file_name[PATH_MAX];
	char line_copy[PATH_MAX];
	int file_index;
	pthread_mutex_t *mutex;

	file_index = find_file(index);
	synchronized(mainsearch.data_mutex) {
		strcpy(line_copy, current->entries[index].data);
		snprintf(command, sizeof(command), editor,
			extract_line_number(line_copy),
			remove_double_appearance(
				current->entries[file_index].data, '/',
				filtered_file_name),
			pattern);
	}
	system(command);
}


/*************************** DISPLAY ******************************************/
static void printl(int *y, const char *line)
{
	int crop = COLS;
	char cropped_line[PATH_MAX];
	char filtered_line[PATH_MAX];
	char *pos;
	char *buf;
	int length=0;

	strncpy(cropped_line, line, crop);
	cropped_line[COLS] = '\0';

	if (isdigit(cropped_line[0])) {
		pos = strtok_r(cropped_line, ":", &buf);
		attron(COLOR_PAIR(2));
		mvprintw(*y, 0, "%s:", pos);
		length = strlen(pos) + 1;
		attron(COLOR_PAIR(1));
		mvprintw(*y, length, "%s", cropped_line + length);
	} else {
		attron(COLOR_PAIR(5));
		mvprintw(*y, 0, "%s", cropped_line,
			remove_double_appearance(cropped_line, '/', filtered_line));
	}
}

static void display_entry(int *y, int *index, int color)
{
	char filtered_line[PATH_MAX];

	if ((unsigned) *index < current->nbentry) {
		if (!is_file(*index)) {
			if (color == 1) {
				attron(A_REVERSE);
				printl(y, current->entries[*index].data);
				attroff(A_REVERSE);
			} else {
				printl(y, current->entries[*index].data);
			}
		} else {
			attron(A_BOLD);
			if (strcmp(current->directory, "./") == 0)
				printl(y, remove_double_appearance(
					current->entries[*index].data + 3, '/',
					filtered_line));
			else
				printl(y, remove_double_appearance(
					current->entries[*index].data, '/',
					filtered_line));
			attroff(A_BOLD);
		}
	}
}

static void display_entries(int *index, int *cursor)
{
	int i = 0;
	int ptr = 0;

	for (i = 0; i < LINES; i++) {
		ptr = *index + i;
		if (i == *cursor) {
			display_entry(&i, &ptr, 1);
		} else {
			display_entry(&i, &ptr, 0);
		}
	}
}

static void resize(int *index, int *cursor)
{
	clear();
	display_entries(index, cursor);
	refresh();
}

static void page_up(int *index, int *cursor)
{
	clear();
	refresh();
	if (*index == 0)
		*cursor = 0;
	else
		*cursor = LINES - 1;
	*index -= LINES;
	*index = (*index < 0 ? 0 : *index);

	if (is_file(*index + *cursor) && *index != 0)
		*cursor -= 1;

	display_entries(index, cursor);
}

static void page_down(int *index, int *cursor)
{
	int max_index;

	if (current->nbentry == 0)
		return;

	if (current->nbentry % LINES == 0)
		max_index = (current->nbentry - LINES);
	else
		max_index = (current->nbentry - (current->nbentry % LINES));

	if (*index == max_index)
		*cursor = (current->nbentry - 1) % LINES;
	else
		*cursor = 0;

	clear();
	refresh();
	*index += LINES;
	*index = (*index > max_index ? max_index : *index);

	if (is_file(*index + *cursor))
		*cursor += 1;
	display_entries(index, cursor);
}

static void cursor_up(int *index, int *cursor)
{
	if (*cursor == 0) {
		page_up(index, cursor);
		return;
	}

	if (*cursor > 0) {
		*cursor = *cursor - 1;
	}

	if (is_file(*index + *cursor))
		*cursor = *cursor - 1;

	if (*cursor < 0) {
		page_up(index, cursor);
		return;
	}

	display_entries(index, cursor);
}

static void cursor_down(int *index, int *cursor)
{
	if (*cursor == (LINES - 1)) {
		page_down(index, cursor);
		return;
	}

	if (*cursor + *index < (signed) current->nbentry - 1) {
		*cursor = *cursor + 1;
	}

	if (is_file(*index + *cursor))
		*cursor = *cursor + 1;

	if (*cursor > (LINES - 1)) {
		page_down(index, cursor);
		return;
	}

	display_entries(index, cursor);
}

void display_status(void)
{
	char *rollingwheel[4] = {"/", "-", "\\", "|"};
	static int i = 0;

	char nbhits[15];
	attron(COLOR_PAIR(1));
	if (mainsearch.status)
		mvaddstr(0, COLS - 1, rollingwheel[++i%4]);
	else
		mvaddstr(0, COLS - 5, "Done.");
	snprintf(nbhits, 15, "Hits: %d", current->nb_lines);
	mvaddstr(1, COLS - (int)(strchr(nbhits, '\0') - nbhits), nbhits);
}


/*************************** MEMORY HANDLING **********************************/
static void check_alloc(search_t *toinc, int size)
{
	if (toinc->nbentry >= toinc->size) {
		toinc->size += size;
		toinc->entries = realloc(toinc->entries, toinc->size * sizeof(entry_t));
	}
}

static void mainsearch_add_file(const char *file)
{
	char	*new_file;

	check_alloc(&mainsearch, 500);
	new_file = malloc(PATH_MAX * sizeof(char));
	strncpy(new_file, file, PATH_MAX);
	mainsearch.entries[mainsearch.nbentry].data = new_file;
	mainsearch.entries[mainsearch.nbentry].isfile = 1;
	mainsearch.nbentry++;
}

static void mainsearch_add_line(const char *line)
{
	char	*new_line;

	check_alloc(&mainsearch, 500);
	new_line = malloc(LINE_MAX * sizeof(char));
	strncpy(new_line, line, LINE_MAX);
	mainsearch.entries[mainsearch.nbentry].data = new_line;
	mainsearch.entries[mainsearch.nbentry].isfile = 0;
	mainsearch.nbentry++;
	mainsearch.nb_lines++;
		if (mainsearch.nbentry <= (unsigned) (current->index + LINES)
			&& current == &mainsearch)
		display_entries(&mainsearch.index, &mainsearch.cursor);
}


/*************************** PARSING ******************************************/
static int is_regex_valid(search_t *cursearch)
{
	regex_t	*reg;

	reg = malloc(sizeof(regex_t));
	if (regcomp(reg, cursearch->pattern, 0)) {
		free(reg);
		return 0;
	} else {
		mainsearch.regex = reg;
		return 1;
	}

	return 1;
}

char * regex(const char *line, const char *pattern)
{
	int ret;

	S_VAR_NOT_USED(pattern);
	ret = regexec(current->regex, line, 0, NULL, 0);

	if (ret != REG_NOMATCH)
		return "1";
	else
		return NULL;
}

static int parse_file(const char *file, const char *pattern, char *options)
{
	FILE *f;
	char line[LINE_MAX];
	char full_line[LINE_MAX];
	int first;
	int line_number;
	char * (*parser)(const char *, const char*);
	errno = 0;

	f = fopen(file, "r");
	if (f == NULL) {
		return -1;
	}

	if (strstr(options, "-i") == NULL) {
		parser = strstr;
	} else {
		parser = strcasestr;
	}

	if (current->is_regex) {
		parser = regex;
	}

	first = 1;
	line_number = 1;
	while (fgets(line, sizeof(line), f)) {
		if (parser(line, pattern) != NULL) {
			if (first) {
				mainsearch_add_file(file);
				first = 0;
			}
			if (line[strlen(line) - 2] == '\r')
				line[strlen(line) - 2] = '\0';
			snprintf(full_line, LINE_MAX, "%d:%s", line_number, line);
			mainsearch_add_line(full_line);
		}
		line_number++;
	}
	fclose(f);
	return 0;
}

static void lookup_file(const char *file, const char *pattern, char *options)
{
	errno = 0;
	pthread_mutex_t		*mutex;
	extension_list_t	*curext;

	if (mainsearch_attr.raw) {
		synchronized(mainsearch.data_mutex)
			parse_file(file, pattern, options);
		return;
	}

	if (is_specific_file(file)) {
		synchronized(mainsearch.data_mutex)
			parse_file(file, pattern, options);
		return;
	}

	curext = mainsearch_attr.firstext;
	while (curext) {
		if (!strcmp(curext->ext, file + strlen(file) - strlen(curext->ext))) {
				synchronized(mainsearch.data_mutex)
				parse_file(file, pattern, options);
			break;
		}
		curext = curext->next;
	}
}

static void lookup_directory(const char *dir, const char *pattern, char *options)
{
	DIR *dp;

	dp = opendir(dir);
	if (!dp) {
		return;
	}

	while (1) {
		struct dirent *ep;
		ep = readdir(dp);

		if (!ep)
			break;

		if (!(ep->d_type & DT_DIR) && is_dir_good(ep->d_name)) {
			char file_path[PATH_MAX];
			snprintf(file_path, PATH_MAX, "%s/%s", dir,
				ep->d_name);

			if (!is_simlink(file_path) || mainsearch_attr.follow_symlinks)
				lookup_file(file_path, pattern, options);
		}

		if (ep->d_type & DT_DIR && is_dir_good(ep->d_name)) {
			char path_dir[PATH_MAX] = "";
			snprintf(path_dir, PATH_MAX, "%s/%s", dir, ep->d_name);
			lookup_directory(path_dir, pattern, options);
		}
	}
	closedir(dp);
}

void * lookup_thread(void *arg)
{
	search_t *d = (search_t *) arg;

	if (isfile(d->directory)) {
		lookup_file(d->directory, d->pattern, d->options);
	} else {
		lookup_directory(d->directory, d->pattern, d->options);
	}

	d->status = 0;
	return (void *) NULL;
}


/*************************** SUBSEARCH ****************************************/
void subsearch_window(char *search)
{
	WINDOW	*searchw;
	int	j = 0, car;

	searchw = newwin(3, 50, (LINES-3)/2 , (COLS-50)/2);
	box(searchw, 0,0);
	wrefresh(searchw);
	refresh();

	mvwprintw(searchw, 1, 1, "To search:");
	while ((car = wgetch(searchw)) != '\n' && j < LINE_MAX) {
		if (car == 8 || car == 127) { //backspace
			if (j > 0)
				search[--j] = 0;
			mvwprintw(searchw, 1, 1, "To search: %s ", search);
			continue;
		}

		if (car == 27) { //escape
			memset(search, 0, LINE_MAX);
			break;
		}

		search[j++] = car;
		mvwprintw(searchw, 1, 1, "To search: %s", search);
	}
	search[j] = 0;
	delwin(searchw);
}

search_t * subsearch(search_t *father)
{
	search_t	*child;
	unsigned int	i;
	char		*search;
	bool		orphan_file = 0;
	char		*new_data;

	search = malloc(LINE_MAX * sizeof(char));
	memset(search, '\0', LINE_MAX);
	subsearch_window(search);

	/*Verify search is not empty*/
	if (search[0] == 0)
		return NULL;

	/* create and init subsearch */
	if ((child = malloc(sizeof(search_t))) == NULL)
		exit(1);

	init_searchstruct(child);
	child->father = father;
	father->child = child;
	child->entries = calloc(100, sizeof(entry_t));
	strncpy(child->pattern, search, LINE_MAX);
	free(search);

	if (!is_regex_valid(child))
		return NULL;

	for (i = 0; i < father->nbentry; i++) {
		if (is_file(i)) {
			/* previous file had no entries, free it */
			if (orphan_file)
				free(new_data);

			/* prepare entry.data but don't add it yet */
			new_data = malloc(LINE_MAX * sizeof(char));
			strncpy(new_data, father->entries[i].data, LINE_MAX);
			orphan_file = 1;
		} else if (regex(father->entries[i].data, child->pattern)) {
			check_alloc(child, 100);
			/* file has entries, add it */
			if (orphan_file) {
				child->entries[child->nbentry].data = new_data;
				child->entries[child->nbentry].isfile = 1;
				child->nbentry++;
				orphan_file = 0;
			}
			/* now add line */
			new_data = malloc(LINE_MAX * sizeof(char));
			strncpy(new_data, father->entries[i].data, LINE_MAX);
			child->entries[child->nbentry].data = new_data;
			child->entries[child->nbentry].isfile = 0;
			child->nb_lines++;
			child->nbentry++;
		}
	}

	child->entries = realloc(child->entries, child->nbentry * sizeof(entry_t));
	child->size = child->nbentry;

	return child;
}


/*************************** CLEANUP ******************************************/
void clean_search(search_t *search)
{
	unsigned int i;

	for (i = 0; i < search->nbentry; i++) {
		free(search->entries[i].data);
	}
	free(search->entries);
//	free(search); //wont work cuz mainsearch ain't no pointer yo
}

void clean_all(void)
{
	search_t	*next;
	exclude_list_t	*curex, *tmpex;
	extension_list_t *curext, *tmpext;
	specific_files_t *curspec, *tmpspec;

	/* free linked list of excludes, extensions, specifics */
	curex = mainsearch_attr.firstexcl;
	while (curex) {
		tmpex = curex;
		curex = curex->next;
		free(tmpex);
	}

	curext = mainsearch_attr.firstext;
	while (curext) {
		tmpext = curext;
		curext = curext->next;
		free(tmpext);
	}

	curspec = mainsearch_attr.firstspec;
	while (curspec) {
		tmpspec = curspec;
		curspec = curspec->next;
		free(tmpspec);
	}

	/* free all search structs */
	do {
		next = current->father;
		clean_search(current);
		current = next;
	} while (next != NULL);
}

static void ncurses_stop()
{
	endwin();
}

static void sig_handler(int signo)
{
	if (signo == SIGINT) {
		ncurses_stop();
		clean_all();
		exit(-1);
	}
}


int main(int argc, char *argv[])
{
	int ch;
	int first = 0;
	const char *editor = NULL;
	pthread_mutex_t *mutex;
	search_t *tmp;
	specific_files_t	*curspec = NULL;
	extension_list_t	*curext = NULL;
	exclude_list_t		*curexcl= NULL;

	current = &mainsearch;
	init_searchstruct(&mainsearch);
	pthread_mutex_init(&mainsearch.data_mutex, NULL);
	get_config(editor, &curext, &curspec);
	get_args(argc, argv, &curext, &curexcl);

	if (argc - optind < 1 || argc - optind > 2) {
		usage();
	}

	for ( ; optind < argc; optind++) {
		if (!first) {
			strcpy(mainsearch.pattern, argv[optind]);
			first = 1;
		} else {
			strcpy(mainsearch.directory, argv[optind]);
		}
	}

	if (mainsearch.is_regex && !is_regex_valid(&mainsearch)) {
		fprintf(stderr, "Bad regexp\n");
		goto quit;
	}

	signal(SIGINT, sig_handler);

	mainsearch.entries = (entry_t *) calloc(mainsearch.size, sizeof(entry_t));

	if (pthread_create(&pid, NULL, &lookup_thread, &mainsearch)) {
		fprintf(stderr, "ngp: cannot create thread");
		clean_search(&mainsearch);
		exit(-1);
	}

	ncurses_init();

	synchronized(mainsearch.data_mutex)
		display_entries(&mainsearch.index, &mainsearch.cursor);

	while ((ch = getch())) {
		switch(ch) {
		case KEY_RESIZE:
			synchronized(mainsearch.data_mutex)
				resize(&current->index, &current->cursor);
			break;
		case CURSOR_DOWN:
		case KEY_DOWN:
			synchronized(mainsearch.data_mutex)
				cursor_down(&current->index, &current->cursor);
			break;
		case CURSOR_UP:
		case KEY_UP:
			synchronized(mainsearch.data_mutex)
				cursor_up(&current->index, &current->cursor);
			break;
		case KEY_PPAGE:
		case PAGE_UP:
			synchronized(mainsearch.data_mutex)
				page_up(&current->index, &current->cursor);
			break;
		case KEY_NPAGE:
		case PAGE_DOWN:
			synchronized(mainsearch.data_mutex)
				page_down(&current->index, &current->cursor);
			break;
		case '/':
			tmp = subsearch(current);
			clear();
			if (tmp != NULL)
				current = tmp;
			display_entries(&current->index, &current->cursor);
			break;
		case ENTER:
		case '\n':
			ncurses_stop();
			open_entry(current->cursor + current->index, editor,
				current->pattern);
			ncurses_init();
			resize(&current->index, &current->cursor);
			break;
		case QUIT:
			if (current->father == NULL) {
				goto quit;
			} else {
				tmp = current->father;
				clean_search(current);
				current = tmp;
				current->child = NULL;
				clear();
				display_entries(&current->index, &current->cursor);
			}
		default:
			break;
		}

		usleep(10000);
		refresh();
		synchronized(mainsearch.data_mutex) {
			display_status();
		}

		synchronized(mainsearch.data_mutex) {
			if (mainsearch.status == 0 && mainsearch.nbentry == 0) {
				goto quit;
			}
		}
	}

quit:
	ncurses_stop();
	clean_all();
	return 0;
}

