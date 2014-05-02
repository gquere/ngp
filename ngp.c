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

#define CURSOR_UP	'k'
#define CURSOR_DOWN	'j'
#define PAGE_UP		'K'
#define PAGE_DOWN	'J'
#define ENTER		'p'
#define QUIT		'q'

#ifdef LINE_MAX
	#undef LINE_MAX
#endif
#define LINE_MAX	256

#define S_VAR_NOT_USED(x) do{(void)(x);}while(0);

#define synchronized(MUTEX) \
for(mutex = &MUTEX; \
mutex && !pthread_mutex_lock(mutex); \
pthread_mutex_unlock(mutex), mutex = 0)

struct entry {
	char *data;
	char isfile:1;
};

struct exclude_list {
	ino_t			d_ino;
	struct exclude_list	*next;
};

struct extension_list {
	char			ext[LINE_MAX];
	struct extension_list	*next;
};

struct specific_files {
	char			spec[LINE_MAX];
	struct specific_files	*next;
};

struct search {
	/* screen */
	int index;
	int cursor;

	/* data */
	struct entry *entries;
	unsigned int nbentry;
	unsigned int nb_lines;
	unsigned int size;

	/* thread */
	pthread_mutex_t data_mutex;
	unsigned int status:1;

	/* search */
	char directory[PATH_MAX];
	char pattern[LINE_MAX];
	unsigned int is_regex:1;
	regex_t *regex;

	/* search in search */
	struct search *father;
	struct search *child;
};

/* attributes specific to mainsearch */
struct mainsearch_attr {
	unsigned int raw:1;
	unsigned int follow_symlinks:1;
	unsigned int has_excludes:1;
	unsigned int is_insensitive:1;

	struct exclude_list	*firstexcl;
	struct specific_files	*firstspec;
	struct extension_list	*firstext;
};

static struct search		mainsearch;
static struct mainsearch_attr	mainsearch_attr;
static struct search		*current;
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

static void init_searchstruct(struct search *searchstruct)
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

static const char * get_config(struct extension_list **curext,
		struct specific_files **curspec)
{
	char *ptr;
	char *buf;
	config_t cfg;
	const char *specific_files;
	const char *extensions;
	struct specific_files *tmpspec;
	struct extension_list *tmpext;
	char *env_editor = NULL;
	char *ptr_env;
	const char *editor_cmd;

	/* get EDITOR environment variable */
	env_editor = getenv("EDITOR");
	if (env_editor) {
		if (!(ptr_env = strrchr(env_editor, '/')))
			ptr_env = env_editor;
	} else {
		ptr_env = "vim";
	}

	/* grab editor string from /etc/ngprc */
	configuration_init(&cfg);
	if (!config_lookup_string(&cfg, ptr_env, &editor_cmd)) {
		fprintf(stderr, "ngprc: no editorcmd string found for %s !\n", ptr_env);
		fprintf(stderr, "please submit a bug for ngp to support your editor\n");
		config_lookup_string(&cfg, "vim", &editor_cmd);
	}

	/* grab list of specific files from /etc/ngprc */
	if (!config_lookup_string(&cfg, "files", &specific_files)) {
		fprintf(stderr, "ngprc: no files string found!\n");
		exit(-1);
	}

	/* get specific files names from configuration */
	ptr = strtok_r((char *) specific_files, " ", &buf);
	while (ptr != NULL) {
		tmpspec = malloc(sizeof(struct specific_files));
		if (!mainsearch_attr.firstspec) {
			mainsearch_attr.firstspec = tmpspec;
		} else {
			(*curspec)->next = tmpspec;
		}

		strncpy(tmpspec->spec, ptr, LINE_MAX);
		tmpspec->next = NULL;
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
		tmpext = malloc(sizeof(struct extension_list));
		if (!mainsearch_attr.firstext) {
			mainsearch_attr.firstext = tmpext;
		} else {
			(*curext)->next = tmpext;
		}

		strncpy(tmpext->ext, ptr, LINE_MAX);
		tmpext->next = NULL;
		*curext = tmpext;
		ptr = strtok_r(NULL, " ", &buf);
	}

	return editor_cmd;
}

//FIXME: move to utils
static ino_t get_inode_from_path(const char *path)
{
	struct stat buf;

	if (stat(path, &buf) != 0) {
		return 0;
	}

	return buf.st_ino;
}

static void get_args(int argc, char *argv[], struct extension_list **curext,
			struct exclude_list **curexcl)
{
	int opt;
	struct exclude_list	*tmpexcl;
	struct extension_list	*tmpext, *tmpext2;
	struct specific_files	*curspec, *tmpspec;

	while ((opt = getopt(argc, argv, "hio:t:refx:")) != -1) {
		switch (opt) {
		case 'h':
			usage();
			break;
		case 'i':
			mainsearch_attr.is_insensitive = 1;
			break;
		case 'o':
			/* free extension list */
			tmpext = mainsearch_attr.firstext;
			while (tmpext) {
				tmpext2 = tmpext;
				tmpext = tmpext->next;
				free(tmpext2);
			}
			mainsearch_attr.firstext = NULL;

			/* free specific list */
			curspec = mainsearch_attr.firstspec;
			while (curspec) {
				tmpspec = curspec;
				curspec = curspec->next;
				free(tmpspec);
			}
			mainsearch_attr.firstspec = NULL;
			/* deliberate fall-through */
		case 't':
			//FIXME: maybe the LL is empty hehe ...
			tmpext = malloc(sizeof(struct extension_list));
			strncpy(tmpext->ext, optarg, LINE_MAX);
			tmpext->next = NULL;
			if (!mainsearch_attr.firstext) {
				mainsearch_attr.firstext = tmpext;
			} else {
				(*curext)->next = tmpext;
			}
			tmpext->next = NULL;
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
			tmpexcl = malloc(sizeof(struct exclude_list));
			if (!mainsearch_attr.firstexcl) {
				mainsearch_attr.has_excludes = 1;
				mainsearch_attr.firstexcl = tmpexcl;
			} else {
				(*curexcl)->next = tmpexcl;
			}

			tmpexcl->d_ino = get_inode_from_path(optarg);
			tmpexcl->next = NULL;
			*curexcl = tmpexcl;
			break;
		default:
			exit(-1);
			break;
		}
	}
}


/*************************** UTILS ********************************************/
static int is_file(int index, struct search *cursearch)
{
	return cursearch->entries[index].isfile;
}

static int isfile(char *nodename)
{
	struct stat buf;

	stat(nodename, &buf);
	return !S_ISDIR(buf.st_mode);
}

static int is_dir_exclude(const ino_t d_ino)
{
	struct exclude_list *curex;

	/* check if directory has been excluded */
	if (mainsearch_attr.has_excludes) {
		curex = mainsearch_attr.firstexcl;
		while (curex) {
			if (d_ino == curex->d_ino) {
				return 1;
			}
			curex = curex->next;
		}
	}

	return 0;
}

static int is_dir_special (const char *dir) {
	/* check if directory shouldn't be browsed at all */
	return  !(strcmp(dir, ".") &&
		strcmp(dir, "..") &&
		strcmp(dir, ".git") &&
		strcmp(dir, ".svn"));
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
	struct specific_files *curspec;

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
	fprintf(stderr, " -t type : add an extension to the list\n");
	fprintf(stderr, " -o type : look for this extension only\n");
	fprintf(stderr, " -e : pattern is a regexp\n");
	fprintf(stderr, " -x folder : exclude directory from search\n");
	fprintf(stderr, " -f : follow symlinks (default doesn't)\n");
	exit(-1);
}

static int find_file(int index)
{
	while (!is_file(index, current))
		index--;

	return index;
}

/* escape '/' and ''' characters for vim search command */
static char * vim_sanitize(const char *search_pattern)
{
	int	i = 0, j = 0;
	char	*sanitized_pattern;
	size_t	size;

	size = strlen(search_pattern) + 1;
	sanitized_pattern = (char *) malloc(size);

	while (search_pattern[i]) {
		if (search_pattern[i] == '/' || search_pattern[i] == '\'') {
			size++;
			sanitized_pattern = realloc(sanitized_pattern, size);
			sanitized_pattern[j] = '\\';
			j++;
		}
		sanitized_pattern[j] = search_pattern[i];
		i++;
		j++;
	}
	sanitized_pattern[j] = 0;

	return sanitized_pattern;
}

static void open_entry(int index, const char *editor_cmd, const char *pattern)
{
	char command[PATH_MAX];
	char filtered_file_name[PATH_MAX];
	char line_copy[PATH_MAX];
	int file_index;
	pthread_mutex_t *mutex;
	char *sanitized_pattern;

	sanitized_pattern = vim_sanitize(pattern);

	file_index = find_file(index);
	synchronized(mainsearch.data_mutex) {
		strcpy(line_copy, current->entries[index].data);
		snprintf(command, sizeof(command), editor_cmd,
			extract_line_number(line_copy),
			remove_double_appearance(
				current->entries[file_index].data, '/',
				filtered_file_name),
			sanitized_pattern,
			mainsearch_attr.is_insensitive ? "\\c" : "");
	}
	system(command);
	free(sanitized_pattern);
}


/*************************** DISPLAY ******************************************/
static void print_line(int *y, char *line)
{
	char *pos, *buf, *pattern, *ptr;
	int length = 0;

	/* line number */
	pos = strtok_r(line, ":", &buf);
	attron(COLOR_PAIR(2));
	mvprintw(*y, 0, "%s:", pos);

	/* line */
	length = strlen(pos) + 1;
	attron(COLOR_PAIR(1));
	mvprintw(*y, length, "%s", line + length);

	pattern = strcasestr(line + length, current->pattern);
	ptr = line + length;

	move(*y, length);
	while (ptr != pattern) {
		addch(*ptr);
		ptr++;
	}

	attron(COLOR_PAIR(4));
	printw("%s", current->pattern);
}

static void print_file(int *y, char *line)
{
	attron(COLOR_PAIR(5));
	mvprintw(*y, 0, "%s", line);
}

static void display_entry(int *y, int *index, int color)
{
	char filtered_line[PATH_MAX];

	if ((unsigned) *index < current->nbentry) {
		if (!is_file(*index, current)) {
			if (color == 1) {
				attron(A_REVERSE);
				print_line(y, current->entries[*index].data);
				attroff(A_REVERSE);
			} else {
				print_line(y, current->entries[*index].data);
			}
		} else {
			attron(A_BOLD);
			print_file(y, remove_double_appearance(current->entries[*index].data, '/', filtered_line));
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

	if (is_file(*index + *cursor, current) && *index != 0)
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

	if (is_file(*index + *cursor, current))
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

	if (is_file(*index + *cursor, current))
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

	if (is_file(*index + *cursor, current))
		*cursor = *cursor + 1;

	if (*cursor > (LINES - 1)) {
		page_down(index, cursor);
		return;
	}

	display_entries(index, cursor);
}

static void display_status(void)
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
static void check_alloc(struct search *toinc, int size)
{
	if (toinc->nbentry >= toinc->size) {
		toinc->size += size;
		toinc->entries = realloc(toinc->entries, toinc->size * sizeof(struct entry));
	}
}

static void mainsearch_add_file(const char *file)
{
	char *new_file;

	check_alloc(&mainsearch, 500);
	new_file = malloc(PATH_MAX * sizeof(char));
	strncpy(new_file, file, PATH_MAX);
	mainsearch.entries[mainsearch.nbentry].data = new_file;
	mainsearch.entries[mainsearch.nbentry].isfile = 1;
	mainsearch.nbentry++;
}

static void mainsearch_add_line(const char *line)
{
	char *new_line;

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
static int is_regex_valid(struct search *cursearch)
{
	regex_t	*reg;

	reg = malloc(sizeof(regex_t));
	if (regcomp(reg, cursearch->pattern, 0)) {
		free(reg);
		return 0;
	} else {
		cursearch->regex = reg;
	}

	return 1;
}

static char * regex(const char *line, const char *pattern)
{
	int ret;

	S_VAR_NOT_USED(pattern);
	ret = regexec(current->regex, line, 0, NULL, 0);

	if (ret != REG_NOMATCH)
		return "1";
	else
		return NULL;
}

static int parse_file(const char *file, const char *pattern)
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

	if (mainsearch_attr.is_insensitive == 0) {
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
		/* check line has a \n */
		//FIXME this is ugly
		if (line[strlen(line) - 1] == '\n')
			line_number++;
		memset(line, 0, LINE_MAX);
	}
	fclose(f);
	return 0;
}

static void lookup_file(const char *file, const char *pattern)
{
	errno = 0;
	pthread_mutex_t		*mutex;
	struct extension_list	*curext;

	if (mainsearch_attr.raw) {
		synchronized(mainsearch.data_mutex)
			parse_file(file, pattern);
		return;
	}

	if (is_specific_file(file)) {
		synchronized(mainsearch.data_mutex)
			parse_file(file, pattern);
		return;
	}

	curext = mainsearch_attr.firstext;
	while (curext) {
		if (!strcmp(curext->ext, file + strlen(file) - strlen(curext->ext))) {
				synchronized(mainsearch.data_mutex)
				parse_file(file, pattern);
			break;
		}
		curext = curext->next;
	}
}

static void lookup_directory(const char *dir, const char *pattern)
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

		/* file */
		if (!(ep->d_type & DT_DIR)) {
			char file_path[PATH_MAX];
			snprintf(file_path, PATH_MAX, "%s/%s", dir,
				ep->d_name);

			if (!is_simlink(file_path) || mainsearch_attr.follow_symlinks)
				lookup_file(file_path, pattern);
		}

		/* directory */
		if (ep->d_type&DT_DIR && !is_dir_special(ep->d_name)) {
			if (!is_dir_exclude(ep->d_ino)) {
				char path_dir[PATH_MAX] = "";
				snprintf(path_dir, PATH_MAX, "%s/%s", dir, ep->d_name);
				lookup_directory(path_dir, pattern);
			}
		}
	}
	closedir(dp);
}

static void * lookup_thread(void *arg)
{
	struct search *d = (struct search *) arg;

	if (isfile(d->directory)) {
		parse_file(d->directory, d->pattern);
	} else {
		lookup_directory(d->directory, d->pattern);
	}

	d->status = 0;
	return (void *) NULL;
}


/*************************** SUBSEARCH ****************************************/
static void subsearch_window(char *search)
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

static struct search * subsearch(struct search *father)
{
	struct search	*child;
	unsigned int	i;
	char		*search;
	bool		orphan_file = 0;
	char		*new_data;

	search = malloc(LINE_MAX * sizeof(char));
	memset(search, 0, LINE_MAX);
	subsearch_window(search);

	/*Verify search is not empty*/
	if (search[0] == 0)
		return NULL;

	/* create and init subsearch */
	if ((child = malloc(sizeof(struct search))) == NULL)
		exit(1);

	init_searchstruct(child);
	child->father = father;
	father->child = child;
	child->entries = calloc(100, sizeof(struct entry));
	strncpy(child->pattern, search, LINE_MAX);
	free(search);

	if (!is_regex_valid(child))
		return NULL;
	current = child;

	for (i = 0; i < father->nbentry; i++) {
		if (is_file(i, father)) {
			/* previous file had no entries, free it */
			if (orphan_file)
				free(new_data);

			/* prepare entry.data but don't add it yet */
			new_data = malloc(LINE_MAX * sizeof(char));
			strncpy(new_data, father->entries[i].data, LINE_MAX);
			orphan_file = 1;
		} else if (regex(father->entries[i].data, child->pattern)) {
			//check_alloc(child, 100); //FIXME this should work ...
			if (child->nbentry%100 >= 98) {
				child->size += 100;
				child->entries = realloc(child->entries, child->size * sizeof(struct entry));
			}
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

	child->entries = realloc(child->entries, child->nbentry * sizeof(struct entry));
	child->size = child->nbentry;

	return child;
}


/*************************** CLEANUP ******************************************/
static void clean_search(struct search *search)
{
	unsigned int i;

	for (i = 0; i < search->nbentry; i++) {
		free(search->entries[i].data);
	}
	free(search->entries);
	free(search->regex);
//	free(search); //wont work cuz mainsearch ain't no pointer yo
}

static void clean_all(void)
{
	struct search		*next;
	struct exclude_list	*curex, *tmpex;
	struct extension_list	*curext, *tmpext;
	struct specific_files	*curspec, *tmpspec;

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

	next = current->father;
	while (next) {
		next = current->father;
		clean_search(current);
		current = next;
	}
}

static void ncurses_stop()
{
	endwin();
}

static void sig_handler(int signo)
{
	if (signo == SIGINT) {
		pthread_kill(pid, SIGINT);
		ncurses_stop();
		clean_all();
		exit(-1);
	}
}


int main(int argc, char *argv[])
{
	int ch;
	int first = 0;
	const char *editor_cmd;
	pthread_mutex_t *mutex;
	struct search *tmp;
	struct specific_files	*curspec = NULL;
	struct extension_list	*curext = NULL;
	struct exclude_list	*curexcl= NULL;

	current = &mainsearch;
	init_searchstruct(&mainsearch);
	pthread_mutex_init(&mainsearch.data_mutex, NULL);
	editor_cmd = get_config(&curext, &curspec);
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

	mainsearch.entries = (struct entry *) calloc(mainsearch.size, sizeof(struct entry));

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
			if (current->nbentry == 0) {
				break;
			}
			ncurses_stop();
			open_entry(current->cursor + current->index, editor_cmd,
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

