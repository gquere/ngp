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
#include <sys/stat.h>
#include <pthread.h>
#include <ctype.h>
#include <regex.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <semaphore.h>

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

#define DEBUG_PERF	0

/*************************** DATA STRUCTURES **********************************/
/* stores an entry, a file or a line */
struct entry {
	char *data;
	unsigned int line;
};

/* contains the directories to exclude from search */
struct exclude_list {
	ino_t			d_ino;
	struct exclude_list	*next;
};

/* contains the file extensions to include in search */
struct extension_list {
	char			ext[LINE_MAX];
	struct extension_list	*next;
};

/* contains the specific files to include in search */
struct specific_files {
	char			spec[LINE_MAX];
	struct specific_files	*next;
};

/* represents a unique search from which other searches may derive from */
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
	char * (*parser)(const char *, const char*, int);
	char directory[PATH_MAX];
	char pattern[LINE_MAX];
	int d, hp; // Rabin-Karp parameters
	int psize; // pattern size used by RK
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

/* colors used by ncurse */
enum colors {
	normal = 1,
	yellow,
	red,
	magenta,
	green,
};

static struct search		*mainsearch;
static struct mainsearch_attr	mainsearch_attr;
static struct search		*current;
static pthread_t		pid = 0, pid_w1, pid_w2, pid_s;

static void usage(void);


/*************************** INIT *********************************************/
/**
 * Initialize a seach structure with default values
 *
 * @param searchstruct	new search structure to init
 */
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

/**
 * Start a ncurse session
 */
static void ncurses_init()
{
	initscr();
	cbreak();
	noecho();
	keypad(stdscr, TRUE);
	nodelay(stdscr, TRUE);
	start_color();
	use_default_colors();
	init_pair(normal, -1, -1);
	init_pair(yellow, COLOR_YELLOW, -1);
	init_pair(red, COLOR_RED, -1);
	init_pair(magenta, COLOR_MAGENTA, -1);
	init_pair(green, COLOR_GREEN, -1);
	curs_set(0);
}

/**
 * ngp relies on the configuration file /etc/ngprc
 * This file is parsed at boot and  its content are copied and converted in
 * the local structures.
 *
 * This file contains the editor commands, the extensions to search and
 * the specific files to include in the search
 *
 * @param curext	linked list that contains the extensions to search
 * @param curspec	linked list that contains the specific files to search
 */
static const char * get_config(struct extension_list **curext,
		struct specific_files **curspec)
{
	FILE *config;
	char configline[256];
	char *env_editor = NULL;
	char *ptr, *ptr_env;
	char *start, *end;
	char *editor_cmd = NULL;
	const char *specific_files = NULL;
	const char *extensions = NULL;
	struct specific_files *tmpspec;
	struct extension_list *tmpext;

	/* get EDITOR environment variable */
	env_editor = getenv("EDITOR");
	if (env_editor) {
		if (!(ptr_env = strrchr(env_editor, '/')))
			ptr_env = env_editor;
	} else {
		ptr_env = "vim";
	}

	/* open config file */
	config = fopen("/etc/ngprc", "r");
	if (!config)
		config = fopen("./ngprc", "r");
	if (!config) {
		fprintf(stderr, "Failed finding ngprc config file\n");
		exit(-1);
	}

	/* parse config file */
	while (fgets(configline, 256, config)) {
		if (!strchr(configline, ';'))
			continue;

		/* editor string contains system command for editor */
		if (strstr(configline, ptr_env)) {
			start = strchr(configline, '"') + 1;
			end = strchr(start, '"');
			end[0] = 0;
			editor_cmd = strdup(start);
		}

		/* files is the list of special files to search */
		if (strstr(configline, "files")) {
			start = strchr(configline, '"') + 1;
			end = strchr(start, '"');
			end[0] = 0;

			ptr = strtok_r((char *) specific_files, " ", &start);
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
				ptr = strtok_r(NULL, " ", &start);
			}
		}

		/* extensions is the list of file types to search */
		if (strstr(configline, "extensions")) {
			start = strchr(configline, '"') + 1;
			end = strchr(start, '"');
			end[0] = 0;

			ptr = strtok_r((char *) extensions, " ", &start);
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
				ptr = strtok_r(NULL, " ", &start);
			}
		}
	}

	fclose(config);

	return (const char *) editor_cmd;
}

//FIXME: move to utils
/**
 * Some folders should be excluded but they are given from a local position
 * we need to translate in an absolute position since the directory parsing is
 * recursive. Therefore convert local path to inode and exclude inodes.
 *
 * @param path	local path of directory
 * @return	inode of directory
 */
static ino_t get_inode_from_path(const char *path)
{
	struct stat buf;

	if (stat(path, &buf) != 0) {
		return 0;
	}

	return buf.st_ino;
}

/**
 * Parse the arguments received via command line
 *
 * @param argc		number of args
 * @param argv		pointer to array of args
 * @param curext	linked list of extension files (from ngprc)
 * @param curexcl	linked list of ignored directories (empty at this point)
 */
static void get_args(int argc, char *argv[], struct extension_list **curext,
			struct exclude_list **curexcl)
{
	int opt;
	struct exclude_list	*tmpexcl;
	struct extension_list	*tmpext, *tmpext2;
	struct specific_files	*curspec, *tmpspec;

	while ((opt = getopt(argc, argv, "hio:t:refx:")) != -1) {
		switch (opt) {
		case 'h': /* display help */
			usage();
			exit(-1);
			break;
		case 'i': /* insensitive case */
			mainsearch_attr.is_insensitive = 1;
			break;
		case 'o': /* look for one extension only */
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
		case 't': /* add extensions to the list */
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
		case 'r': /* perform raw search (all files) */
			mainsearch_attr.raw = 1;
			break;
		case 'e': /* pattern is a regexp */
			mainsearch->is_regex = 1;
			break;
		case 'f': /* follow symlinks */
			mainsearch_attr.follow_symlinks = 1;
			break;
		case 'x': /* exclude folders from search */
			/* add excludes to the list */
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
			/* shouldn't get here anyways */
			usage();
			exit(-1);
			break;
		}
	}
}


/*************************** UTILS ********************************************/
/**
 * Check if an entry in our local structure is a file
 *
 * @param index		index of entry in the array
 * @param cursearch	pointer to current local structure
 * @return		1 if entry is a file, 0 otherwise
 */
static int is_file(int index, struct search *cursearch)
{
	return !cursearch->entries[index].line;
}

/**
 * Checks if local node is a file
 *
 * @param nodename	node name
 * @return		1 if file, 0 if directory
 */
static int isfile(char *nodename)
{
	struct stat buf;

	stat(nodename, &buf);
	return !S_ISDIR(buf.st_mode);
}

/**
 * Checks if a directory is in the list of excluded directories
 *
 * @param d_ino	inode of directory
 * @return	1 if folder should be ignored, 0 otherwise
 */
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

/**
 * There are some folders that we want to always ignore, such as version
 * control.
 *
 * @param dir	local directory name
 * @output	1 if folder should be ignored, 0 otherwise
 */
static int is_dir_special(const char *dir) {
	/* check if directory shouldn't be browsed at all */
	return  !(strcmp(dir, ".") &&
		strcmp(dir, "..") &&
		strcmp(dir, ".git") &&
		strcmp(dir, ".svn"));
}

/**
 * Checks if a given file is a symlink or not, as we choose to follow them
 * as an option.
 *
 * @param file_path	path of the file
 * @return		1 if file is a symlink, 0 otherwise
 */
static int is_simlink(char *file_path)
{
	struct stat filestat;

	lstat(file_path, &filestat);
	return S_ISLNK(filestat.st_mode);
}

/**
 * We want to include some files that have no extensions, such as Makefiles.
 * Thus, we check before discarding a file whether it's in the list of special
 * files.
 *
 * @param name	file name
 * @return	1 if file needs to be scanned, 0 otherwise
 */
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

/**
 * Depending on where the search is performed, it might be that we store
 * recurring '/' characters because of the path concatenation. For visual
 * display, we want to remove the double appearance of such characters.
 *
 * @param inital	the string to sanitize
 * @param c		the character to strip
 * @param final		the string to write into once clean
 * @return		sanitized string
 */
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

/**
 * Because our search structure is an array and not a linked list,
 * we may need to recover the file that is the container of a line
 * and do so by climbing up the array until a file is found.
 *
 * @param index	index of the line in the array
 */
static int find_file(int index)
{
	while (!is_file(index, current))
		index--;

	return index;
}

/**
 * Escape '/' and ''' characters for vim search command by preceding them by '\'
 *
 * @param search_pattern	string to sanitize
 */
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

/**
 * Opens a line using the editor variable from the /etc/ngprc conf file
 *
 * @param index		line number
 * @param editor_cmd	prefilled editor command
 * @param pattern	pattern to highlight
 */
static void open_entry(int index, const char *editor_cmd, const char *pattern)
{
	char command[PATH_MAX];
	int file_index;
	pthread_mutex_t *mutex;
	char *sanitized_pattern;
	int retval;

	/* vim doesn't like naked / and ' characters, so escape them */
	sanitized_pattern = vim_sanitize(pattern);

	/* find the file associated with the line */
	file_index = find_file(index);

	synchronized(mainsearch->data_mutex) {
		/* fill the editor system command with our variables */
		snprintf(command, sizeof(command), editor_cmd,
			current->entries[index].line,
			current->entries[file_index].data,
			sanitized_pattern,
			mainsearch_attr.is_insensitive ? "\\c" : "");
	}
	retval = system(command);
	S_VAR_NOT_USED(retval);
	free(sanitized_pattern);
}


/*************************** DISPLAY ******************************************/
/**
 * Display a line in ncurses
 *
 * @param y	vertical position the line should be written at
 * @param line	line to write
 */
static void print_line(int *y, char *line, int line_nb)
{
	int number_len;
	char number[10];
	char *pattern;
	char *ptr;

	/* line number */
	number_len = sprintf(number, "%d", line_nb);
	attron(COLOR_PAIR(yellow));
	mvprintw(*y, 0, "%s:", number);

	/* line */
	attron(COLOR_PAIR(normal));
	mvprintw(*y, number_len + 1, "%s", line);

	move(*y, number_len + 1);

	if (current->is_regex)
		return;

	/* find pattern to colorize */
	ptr = line;
	pattern = line;
	// FIXME: could s/if/while but insensitive doesn't like it ?!
	if ((pattern = strcasestr(ptr, current->pattern))) {
		/* move by one char until pattern is found */
		while (ptr != pattern) {
			addch(*ptr);
			ptr++;
		}

		/* print colorized pattern on top of current line */
		attron(COLOR_PAIR(red));
		printw("%s", current->pattern);
		attron(COLOR_PAIR(normal));
		ptr += current->psize - 1;
	}
}

/**
 * Display a file in ncurses
 *
 * @param y	vertical position the file should be written at
 * @param file	file to write
 */
static void print_file(int *y, char *file)
{
	attron(COLOR_PAIR(green));
	mvprintw(*y, 0, "%s", file);
}

/**
 * Display an entry in ncurses, finds entry type and calls corresponding function
 *
 * @param y	vertical position the entry should be printed at
 * @param index	index of the entry in the local array
 * @param color	indicated whether the user currently position its cursor on the entry
 */
static void display_entry(int *y, int *index, int color)
{
	char filtered_line[PATH_MAX];

	if ((unsigned) *index < current->nbentry) {
		if (!is_file(*index, current)) {
			if (color == 1) {
				attron(A_REVERSE);
				print_line(y, current->entries[*index].data, current->entries[*index].line);
				attroff(A_REVERSE);
			} else {
				print_line(y, current->entries[*index].data, current->entries[*index].line);
			}
		} else {
			attron(A_BOLD);
			print_file(y, remove_double_appearance(current->entries[*index].data, '/', filtered_line));
			attroff(A_BOLD);
		}
	}
}

/**
 * Displays a screen worth of entries
 *
 * @param index		current position in the local array
 * @param cursor	current position of user cursor
 */
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

/**
 * //FIXME: we don't need this do we ?
 */
static void resize(int *index, int *cursor)
{
	clear();
	display_entries(index, cursor);
	refresh();
}

/**
 * User pressed PAGE_UP, move one page up
 *
 * @param index		current position in the local array
 * @param cursor	current position of user cursor
 */
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

/**
 * User pressed PAGE_DOWN, move one page down
 *
 * @param index		current position in the local array
 * @param cursor	current position of user cursor
 */
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

/**
 * User pressed KEY_UP, move one entry up
 *
 * @param index		current position in the local array
 * @param cursor	current position of user cursor
 */
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

/**
 * User pressed KEY_DOWN, move one entry down
 *
 * @param index		current position in the local array
 * @param cursor	current position of user cursor
 */
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

/**
 * Display the search status in the top right corner
 */
static void display_status(void)
{
	char *rollingwheel[4] = {"/", "-", "\\", "|"};
	static int i = 0;

	char nbhits[15];
	attron(COLOR_PAIR(normal));
	if (mainsearch->status) {
		mvaddstr(0, COLS - 1, rollingwheel[++i%4]);
	} else {
		mvaddstr(0, COLS - 5, "Done.");
#if DEBUG_PERF
		exit(0);
#endif
	}

	snprintf(nbhits, 15, "Hits: %d", current->nb_lines);
	mvaddstr(1, COLS - (int)(strchr(nbhits, '\0') - nbhits), nbhits);
}


/*************************** MEMORY HANDLING **********************************/
/**
 * Check if the currently allocated size for handling entries if enough,
 * otherwise increase by size.
 *
 * @param toinc	search structure to check size of
 * @param size	size to incremement of if array is too small
 */
static inline void check_alloc(struct search *toinc, int size)
{
	if (toinc->nbentry >= toinc->size) {
		toinc->size += size;
		toinc->entries = realloc(toinc->entries, toinc->size * sizeof(struct entry));
	}
}

/**
 * Add a file to the current search structure
 *
 * @param file	name of file
 */
static void mainsearch_add_file(const char *file)
{
	check_alloc(mainsearch, 500);
	mainsearch->entries[mainsearch->nbentry].data = (char *) file;
	mainsearch->entries[mainsearch->nbentry].line = 0;
	mainsearch->nbentry++;
}

/**
 * Add a line to the current search structure
 *
 * @param line	line to add (including prepended line number)
 */
static void mainsearch_add_line(const char *line, int line_nb)
{
	check_alloc(mainsearch, 500);
	mainsearch->entries[mainsearch->nbentry].data = (char *) line;
	mainsearch->entries[mainsearch->nbentry].line = line_nb;
	mainsearch->nbentry++;
	mainsearch->nb_lines++;

	//FIXME: move check somewhere else because it slows down the search thread
	/* display entries if we're not filled yet on first screen */
	if (mainsearch->nbentry <= (unsigned) (current->index + LINES)
			&& current == mainsearch)
		display_entries(&mainsearch->index, &mainsearch->cursor);
}


/*************************** PARSING ******************************************/
/* We need best performance on regular string search, and it receives size
 * so this function is used to accomodate strcasestr with one more param until
 * I rewrite it. FIXME :)
 */
static char * strcasestr_wrapper(const char *line, const char *pattern, int siz)
{
	S_VAR_NOT_USED(siz);

	return strcasestr(line, pattern);
}

static char * strstr_wrapper(const char *line, const char *pattern, int siz)
{
	S_VAR_NOT_USED(siz);

	return strstr(line, pattern);
}
/**
 * Checks if a regexp is valid
 *
 * @param cursearch	search structure containing the regexp
 * @return		1 if valid, 0 otherwise
 */
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

/**
 * Parse line using a regexp, and offer a prototype akin to strstr to allow use
 * of function pointers
 *
 * @param line		line to parse
 * @param pattern	not used, since stored in search structure
 * @return		NULL if pattern not found, valid string otherwise
 */
static char * regex(const char *line, const char *pattern, int size)
{
	int ret;
	S_VAR_NOT_USED(size);
	S_VAR_NOT_USED(pattern);

	ret = regexec(current->regex, line, 0, NULL, 0);

	if (ret != REG_NOMATCH)
		return "1";
	else
		return NULL;
}

/**
 * Rolling hash function used for this instance of Rabin-Karp
 */
#define REHASH(a,b,h) ((((h) - (a)*mainsearch->d) << 1) + b)

/**
 * Compute Rabin-Karp parameters (shift d and hash(pattern)
 *
 * @param pattern	search pattern
 */
static void pre_rabin_karp(const char *pattern)
{
	int i;
	int psize;

	psize = strlen(pattern);

	/* compute shift */
	mainsearch->d = 1 << (psize - 1);

	/* compute hash(pattern) */
	for (mainsearch->hp = i = 0; i < psize; i++)
		mainsearch->hp = (mainsearch->hp << 1) + pattern[i];

	mainsearch->psize = psize;
}

/**
 * Rabin-Karp algorithm: use a rolling hash over the text to fasten
 * the comparison computation
 *
 * @param text		Haystack
 * @param pattern	Needle
 * @return		pointer to match or NULL
 */
static inline char * rabin_karp(const char *text, const char *pattern, int tsize)
{
	int ht;
	int i;

	/* compute hash(text) at position 0 */
	for (ht = i = 0; i < mainsearch->psize; i++)
		ht = (ht << 1) + text[i];

	for (i = 0; i <= tsize - mainsearch->psize; i++) {
		if (ht == mainsearch->hp) /* got a hash match, but it could be a collision */
			if (!memcmp(pattern, text + i, mainsearch->psize))
				return (char *) text + i;
		/* compute rolling hash for next position */
		ht = REHASH(text[i], text[i + mainsearch->psize], ht);
	}

	return NULL;
}
#if 0
static void pre_shiftor(const char *pattern)
{
	int i;
	int psize;

	psize = strlen(pattern);
	if (psize > 31) {
		pre_rabin_karp(pattern);
		mainsearch->parser = rabin_karp;
		return;
	}

	R = ~1;

	for (i = 0; i < 256; i++)
		mask[i] = ~0;

	for (i = 0; i < psize; i++) {
		if ((int) pattern[i] < 0) {
			pre_rabin_karp(pattern);
			mainsearch->parser = rabin_karp;
			return;
		}

		mask[(int) pattern[i]] &= ~(1UL << i);
	}

	mainsearch->psize = psize;
	mainsearch->d = (1UL << psize);
}

static inline char * shiftor(const char *text, const char *pattern, int tsize)
{
	int i;
	S_VAR_NOT_USED(pattern);
	S_VAR_NOT_USED(tsize);

	i = 0;
	while (text[i]) {
		R |= mask[(int) text[i]];
		R <<= 1;

		if (!(R & mainsearch->d))
			return (char *) text + i - mainsearch->psize + 1;

		i++;
	}

	return NULL;
}
#endif
unsigned long int skipt[256];

static void pre_bmh(const char *pattern)
{
	int i;
	int psize;

	psize = strlen(pattern);
	if (psize == 1) {
		mainsearch->parser = strstr_wrapper;
	}

	for (i = 0; i < 256; i++)
		skipt[i] = psize;

	for (i = 0; i < psize -1; i++) {
		if ((int) pattern[i] < 0) {
			pre_rabin_karp(pattern);
			mainsearch->parser = rabin_karp;
			return;
		}

		skipt[(int) pattern[i]] = psize - i - 1;
	}

	mainsearch->psize = psize;
}

static inline char * bmh(const char *text, const char *pattern, int tsize)
{
	int i;
	int psize;

	psize = mainsearch->psize;

	i = 0;
	while (i <= tsize - psize) {
		if (text[i + psize - 1] == pattern[psize - 1] && text[i] == pattern[0])
			if (!memcmp(text + i + 1, pattern + 1, psize - 2))
				return (char *) text + i;
		if (text[i + psize - 1] > 0)
			i += skipt[(int) text[i + psize - 1]];
		else
			while (text[i + psize - 1] < 0) //unicode
				i += psize;
	}

	return NULL;
}
#if 0
unsigned long int mask;
unsigned int skip;

#define BLOOM(mask, c)		((mask |= (1UL << ((c) & (32 - 1)))))
#define BLOOM_ADD(mask, c)	((mask &= (1UL << ((c) & (32 - 1)))))

static void pre_pfs(const char *pattern)
{
	int i;
	int psize;

	psize = strlen(pattern);
	mask = 0;
	skip = psize - 2;

	for (i = 0; i < psize - 1; i++) {
		if ((int) pattern[i] < 0) {
			pre_rabin_karp(pattern);
			mainsearch->parser = rabin_karp;
			return;
		}
		BLOOM_ADD(mask, pattern[i]);
		if (pattern[i] == pattern[psize - 1])
			skip = psize - i - 2;
	}
	BLOOM_ADD(mask, pattern[psize - 1]);

	mainsearch->psize = psize;
}

static inline char * pfs(const char *text, const char *pattern, int tsize)
{
	int i, j;
	int psize;

	psize = mainsearch->psize;

	for (i = 0; i <= tsize - psize; i++) {
		if (text[i + psize - 1] == pattern[psize - 1]) {
			for (j = 0; j < psize; j++) { //strcmp ??
				if (text[i + j] != pattern[j])
					break;
			}

			if (j == psize)
				return (char *) text + i;

			if (!BLOOM(mask, text[i + psize]))
				i += psize;
			else
				i += skip;
		} else {
			if (!BLOOM(mask, text[i + psize]))
				i += psize;
		}
	}

	return NULL;
}
#endif

struct filep {
	const char *name;
	char *start;
	char *mid;
	unsigned int size;
	unsigned int midline;
};
struct filep filep;

struct worker_result {
	char *line;
	int index;
	struct worker_result *next;
};
struct worker_result *worker_res[2] = {NULL, NULL};

sem_t	new_file_signal;
sem_t	is_data_for_worker[2];
sem_t	worker_data_treated[2];

int th1 = 0; // worker thread numbers
int th2 = 1;
int th3 = 2;

/**
 * Core of ngp, opens file using mmap, does bound checking then signals
 * worker threads that they can parse the file (half each)
 *
 * @param file		path of file to parse
 * @return		0 on success, -1 otherwise
 */
static int parse_file(const char *file)
{
	int f;
	struct stat sb;
	errno = 0;
	char *p;
	char *filename;
	char *mid_newline;

	/* wait for synchronization from data thread*/
	sem_wait(&new_file_signal);

	/* prepare file open using mmap */
	f = open(file, O_RDONLY);
	if (f == -1) {
		sem_post(&new_file_signal);
		return -1;
	}

	if (fstat(f, &sb) < 0) {
		sem_post(&new_file_signal);
		close(f);
		return -1;
	}

	/* check file ain't empty */
	if (!sb.st_size) {
		sem_post(&new_file_signal);
		close(f);
		return -1;
	}

	p = mmap(0, sb.st_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, f, 0);
	if (p == MAP_FAILED) {
		sem_post(&new_file_signal);
		close(f);
		return -1;
	}
	close(f);

	filename = strdup(file); // Need to do this because file overwritten
	filep.name = filename;
	filep.size = sb.st_size;
	filep.start = p;
	mid_newline = strchr(p + sb.st_size / 2, '\n');
	if (!mid_newline) {	// short file that cannot be cut in 2
		filep.mid = p + sb.st_size - 1;
	} else {
		filep.mid = mid_newline + 1;
	}

	/* tell workers they can start processing the file */
	sem_post(&is_data_for_worker[0]);
	sem_post(&is_data_for_worker[1]);

	return 0;
}

/**
 * Check if a file should be parsed for pattern and if so call parse_file
 *
 * @param file		file name
 * @param pattern	pattern to find in file
 */
static void lookup_file(const char *file)
{
	errno = 0;
	pthread_mutex_t		*mutex;
	struct extension_list	*curext;

	/* if the search is of type raw, all file are to be parsed */
	if (mainsearch_attr.raw) {
		synchronized(mainsearch->data_mutex)
			parse_file(file);
		return;
	}

	/* check if file is a specific file */
	if (is_specific_file(file)) {
		synchronized(mainsearch->data_mutex)
			parse_file(file);
		return;
	}

	/* check if file matches the extension list */
	curext = mainsearch_attr.firstext;
	while (curext) {
		if (!strcmp(curext->ext, file + strlen(file) - strlen(curext->ext))) {
				synchronized(mainsearch->data_mutex)
				parse_file(file);
			break;
		}
		curext = curext->next;
	}
}

/**
 * Data thread saves result of worker threads in ngp's result array
 */
static void * save_thread(void * thnum)
{
	int *tnum = (int *) thnum;
	S_VAR_NOT_USED(tnum);
	struct worker_result *res = NULL, *tmp;

	while (1) {
		/* exit if no more files */
		if (!mainsearch->status) {
			return (void *) NULL;
		}

		/* wait for workers to be done */
		sem_wait(&worker_data_treated[0]);
		sem_wait(&worker_data_treated[1]);

		if (worker_res[0] != NULL || worker_res[1] != NULL) {
			mainsearch_add_file(filep.name);
		} else {
			free((void *) filep.name);
		}

		if (worker_res[0] != NULL) {
			res = worker_res[0];
			while (res) {
				mainsearch_add_line(res->line, res->index);
				tmp = res;
				res = res->next;
				free(tmp);
			}
		}

		if (worker_res[1] != NULL) {
			res = worker_res[1];
			while (res) {
				mainsearch_add_line(res->line, res->index + filep.midline); //FIXME: +count mid
				tmp = res;
				res = res->next;
				free(tmp);
			}
		}

		worker_res[0] = NULL;
		worker_res[1] = NULL;
		munmap(filep.start, filep.size); //FIXME
		sem_post(&new_file_signal);
	}

	return NULL;
}

/**
 * Worker threads each parse half a file
 */
static void * worker_thread(void * thnum)
{
	int *tnum = (int *) thnum;
	char *start, *end, *p;
	char *endline;
	struct worker_result *cur_res = NULL, *tmp_res;
	char *tmp_str;
	int first;
	int line_count;
	int line_size;

	while (1) {
		/* exit if no more files */
		if (!mainsearch->status) {
			return (void *) NULL;
		}

		/* wait for work signal from mmaper */
		sem_wait(&is_data_for_worker[*tnum]);

		if (*tnum) {
			start = filep.mid;
			end = filep.start + filep.size;
		} else {
			start = filep.start;
			end = filep.mid - 1;
		}

		p = start;
		first = 1;
		line_count = 1;

		while (p < end && (endline = strchr(p, '\n'))) {
			*endline = '\0';
			if (mainsearch->parser(p, mainsearch->pattern, endline - p)) {
				tmp_res = malloc(sizeof(struct worker_result));
				if (!tmp_res) {
					fprintf(stderr, "no mem for tmp_res");
					exit(-1);
				}

				line_size = (endline - p + 1) >= 256 ? 256 : (endline - p + 1);
				tmp_str = malloc(line_size * sizeof(char));
				if (!tmp_str) {
					fprintf(stderr, "no mem for tmp_str");
					exit(-1);
				}
				strncpy(tmp_str, p, line_size);

				tmp_res->line = tmp_str;
				tmp_res->index = line_count;
				tmp_res->next = NULL;

				if (first) {
					worker_res[*tnum] = tmp_res;
					first = 0;
				} else {
					cur_res->next = tmp_res;
				}
				cur_res = tmp_res;
			}
			line_count++;
			p = endline + 1;
		}
		/* first worker needs to tell where midline was eaxctly */
		if (*tnum == 0)
			filep.midline = line_count - 1;

		/* tell data thread that we're finished parsing the file */
		sem_post(&worker_data_treated[*tnum]);
	}

	return NULL;
}


/**
 * Recursively parses a directory and calls lookup_file if a file is found that
 * matches the criteria of the search
 *
 * @param dir		directory to parse
 */
static void lookup_directory(const char *dir)
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

			/* check if file is a symlink and we should follow it */
			if (!is_simlink(file_path) || mainsearch_attr.follow_symlinks)
				lookup_file(file_path);
		}

		/* directory */
		if (ep->d_type&DT_DIR && !is_dir_special(ep->d_name)) {
			/* check if directory has been excluded from search */
			if (!is_dir_exclude(ep->d_ino)) {
				char path_dir[PATH_MAX] = "";
				snprintf(path_dir, PATH_MAX, "%s/%s", dir, ep->d_name);
				lookup_directory(path_dir);
			}
		}
	}
	closedir(dp);
}

/**
 * Thread spawned by ngp to take care of the memory and the parsing
 * In case the user submitted a file to ngp instead of a directory, parse file
 * immediately. Otherwise, parse the directory.
 *
 * @param arg	search structure (to cast)
 * @return	NULL
 */
static void * lookup_thread(void *arg)
{
	struct search *d = (struct search *) arg;

	if (sem_init(&new_file_signal, 0, 1)) {
		fprintf(stderr, "Error: failed creating semaphore");
		exit(-1);
	}
	if (sem_init(&is_data_for_worker[0], 0, 0)) {
		fprintf(stderr, "Error: failed creating semaphore");
		exit(-1);
	}
	if (sem_init(&is_data_for_worker[1], 0, 0)) {
		fprintf(stderr, "Error: failed creating semaphore");
		exit(-1);
	}
	if (sem_init(&worker_data_treated[0], 0, 0)) {
		fprintf(stderr, "Error: failed creating semaphore");
		exit(-1);
	}
	if (sem_init(&worker_data_treated[1], 0, 0)) {
		fprintf(stderr, "Error: failed creating semaphore");
		exit(-1);
	}

	if (pthread_create(&pid_w1, NULL, &worker_thread, &th1)) {
		fprintf(stderr, "Error: failed creating worker thread");
		exit(-1);
	}
	if (pthread_create(&pid_w2, NULL, &worker_thread, &th2)) {
		fprintf(stderr, "Error: failed creating worker thread");
		exit(-1);
	}
	if (pthread_create(&pid_s, NULL, &save_thread, &th3)) {
		fprintf(stderr, "Error: failed creating worker thread");
		exit(-1);
	}


	if (isfile(d->directory)) {
		parse_file(d->directory);
	} else {
		lookup_directory(d->directory);
	}

	d->status = 0;
	//FIXME: wait for all children ? dunno
	return (void *) NULL;
}


/*************************** SUBSEARCH ****************************************/
/**
 * Spawn a subsearch window for the user to write a new pattern into
 *
 * @param search	current search structure
 */
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

/**
 * Create a subsearch to the current search and make this one the current one
 *
 * @param father	the current search
 * @return		the new current search, child of father
 */
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
			new_data = malloc((strlen(father->entries[i].data) + 1) * sizeof(char));
			strncpy(new_data, father->entries[i].data, (strlen(father->entries[i].data) + 1));
			orphan_file = 1;
		} else if (regex(father->entries[i].data, child->pattern, 0)) {
			//check_alloc(child, 100); //FIXME this should work ...
			if (child->nbentry%100 >= 98) {
				child->size += 100;
				child->entries = realloc(child->entries, child->size * sizeof(struct entry));
			}
			/* file has entries, add it */
			if (orphan_file) {
				child->entries[child->nbentry].data = new_data;
				child->entries[child->nbentry].line = 0;
				child->nbentry++;
				orphan_file = 0;
			}
			/* now add line */
			//FIXME: NO NEED TO MALLOC HERE JUST POINT TO EXISTING STRING
			new_data = malloc((strlen(father->entries[i].data) + 1) * sizeof(char));
			strncpy(new_data, father->entries[i].data, (strlen(father->entries[i].data) + 1));
			child->entries[child->nbentry].data = new_data;
			child->entries[child->nbentry].line = father->entries[i].line;
			child->nb_lines++;
			child->nbentry++;
		}
	}

	child->entries = realloc(child->entries, child->nbentry * sizeof(struct entry));
	child->size = child->nbentry;

	return child;
}


/*************************** CLEANUP ******************************************/
/**
 * Free a search structure
 */
static void clean_search(struct search *search)
{
	unsigned int i;

	/* free the data entries in the array */
	for (i = 0; i < search->nbentry; i++) {
		free(search->entries[i].data);
	}

	/* free the array */
	free(search->entries);

	/* free the rest of the search structure */
	free(search->regex);
	free(search);
}

/**
 * Free all structures used by ngp
 */
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

	/* free all search structures from bottom up */
	next = current->father;
	while (next) {
		next = current->father;
		clean_search(current);
		current = next;
	}
}

/**
 * Stop the ncurses session
 */
static void ncurses_stop()
{
	endwin();
}

/*
 * Cleanly exit ngp
 * THIS FUNCTION IS ATEXIT !!
 */
static void exit_ngp(void)
{
	if (pid)
		pthread_kill(pid, SIGINT);
	ncurses_stop();
	clean_all();
#if DEBUG_PERF
	printf("Found %d hits\n", current->nb_lines);
#endif
}

/**
 * Cleanly stop ngp if CTRL+C is intercepted
 */
static void sig_handler(int signo)
{
	if (signo == SIGINT) {
		/* do note that at this point atexit is registered */
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

	/* set the exit function for main */
	atexit(exit_ngp);

	/* this is the mainsearch, our first search structure */
	mainsearch = malloc(sizeof(struct search));
	if (!mainsearch)
		exit(-1);
	current = mainsearch;
	init_searchstruct(mainsearch);
	memset(&mainsearch_attr, 0, sizeof(struct mainsearch_attr));

	/* we need a mutex to synchronize the display and data threads */
	pthread_mutex_init(&mainsearch->data_mutex, NULL);

	/* get the configuration from /etc/ngprc */
	editor_cmd = get_config(&curext, &curspec);

	/* parse input arguments */
	get_args(argc, argv, &curext, &curexcl);

	if (argc - optind < 1 || argc - optind > 2) {
		usage();
		exit(-1);
	}

	/* copy pattern and optional directory in mainsearch structure */
	for ( ; optind < argc; optind++) {
		if (!first) {
			strcpy(mainsearch->pattern, argv[optind]);
			first = 1;
		} else {
			strcpy(mainsearch->directory, argv[optind]);
		}
	}

	/* if a regexp was given, check now that it is valid */
	if (mainsearch->is_regex) {
		/* position function pointer on appropriate parser */
		mainsearch->parser = regex;
		if (!is_regex_valid(mainsearch)) {
			fprintf(stderr, "Bad regexp\n");
			exit(-1);
		}
	} else if (!mainsearch_attr.is_insensitive) {
		/* compute rabin-karp parameters on pattern */
//		mainsearch->parser = rabin_karp;
//		pre_rabin_karp(mainsearch->pattern);
		mainsearch->parser = bmh;
		pre_bmh(mainsearch->pattern);
		//mainsearch->parser = pfs;
		//pre_pfs(mainsearch->pattern);
	} else {
		mainsearch->parser = strcasestr_wrapper;
	}

	signal(SIGINT, sig_handler);

	/* initialize the entries array for the mainsearch */
	mainsearch->entries = (struct entry *) calloc(mainsearch->size, sizeof(struct entry));

	/* create the data thread, main is now the display thread the user interacts with */
	if (pthread_create(&pid, NULL, &lookup_thread, mainsearch)) {
		fprintf(stderr, "ngp: cannot create thread");
		clean_search(mainsearch);
		exit(-1);
	}

	ncurses_init();

	synchronized(mainsearch->data_mutex)
		display_entries(&mainsearch->index, &mainsearch->cursor);

	while ((ch = getch())) {
		switch(ch) {
		case KEY_RESIZE:
			synchronized(mainsearch->data_mutex)
				resize(&current->index, &current->cursor);
			break;
		case CURSOR_DOWN:
		case KEY_DOWN:
			synchronized(mainsearch->data_mutex)
				cursor_down(&current->index, &current->cursor);
			break;
		case CURSOR_UP:
		case KEY_UP:
			synchronized(mainsearch->data_mutex)
				cursor_up(&current->index, &current->cursor);
			break;
		case KEY_PPAGE:
		case PAGE_UP:
			synchronized(mainsearch->data_mutex)
				page_up(&current->index, &current->cursor);
			break;
		case KEY_NPAGE:
		case PAGE_DOWN:
			synchronized(mainsearch->data_mutex)
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
				exit(-1);
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
		refresh(); //FIXME: what's the point ?
		synchronized(mainsearch->data_mutex) {
			display_status();
		}

		synchronized(mainsearch->data_mutex) {
			if (mainsearch->status == 0 && mainsearch->nbentry == 0) {
				exit(0);
			}
		}
	}

	return 0;
}

