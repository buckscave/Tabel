/* ============================================================
 *  TABEL v0.7
 *  Terminal Spreadsheet
 *  Standar: C89 + POSIX.1-2008
 * ============================================================ */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <termios.h>
#include <signal.h>
#include <sys/ioctl.h>
#include <ctype.h>
#include <errno.h>
#include <math.h>

/* ============================================================
 * Konstanta
 * ============================================================ */
#define MAKS_KOLOM 52
#define MAKS_BARIS 10000
#define MAX_TEXT   1024
#define UNDO_MAX   2048
#define MAX_FORMULA_LENGTH 256
#define MAX_NAMA_FILE 256

/* Unicode garis */
#define TL "\xE2\x94\x8C"
#define TR "\xE2\x94\x90"
#define BL "\xE2\x94\x94"
#define BR "\xE2\x94\x98"
#define TC "\xE2\x94\xAC"
#define BC "\xE2\x94\xB4"
#define LC "\xE2\x94\x9C"
#define RC "\xE2\x94\xA4"
#define CR "\xE2\x94\xBC"
#define H  "\xE2\x94\x80"
#define V  "\xE2\x94\x82"

/* Escape + warna */
#define ESC_CLR  "\033[2J"
#define ESC_HOME "\033[H"
#define ESC_NORM "\033[0m"
#define FG_DARK  "\033[38;2;60;70;80m"
#define FG_WHITE "\033[38;2;255;255;255m"
#define FG_GREEN "\033[38;2;0;200;0m"
#define FG_CYAN  "\033[38;2;0;200;255m"
#define FG_RED   "\033[38;2;200;0;0m"
#define FG_YELLOW "\033[38;2;200;200;0m"
#define FG_GRAY  "\033[38;2;150;150;150m"
#define BG_DARK  "\033[48;2;60;70;80m"

/* Alignment */
enum align { LEFT, CENTER, RIGHT };

/* ============================================================
 * Struktur Data
 * ============================================================ */
struct konfigurasi {
    int kolom;
    int baris;
    int aktif_x;
    int aktif_y;
    int view_col;
    int view_row;
    int prev_x;
    int prev_y;
};

struct op {
    int x;
    int y;
    char before[MAX_TEXT];
    char after[MAX_TEXT];
};

struct buffer {
    char *data;
    size_t size;
    size_t capacity;
};

/* ============================================================
 * Data Global
 * ============================================================ */
static char isi[MAKS_BARIS][MAKS_KOLOM][MAX_TEXT];
static enum align align_sel[MAKS_BARIS][MAKS_KOLOM];
static int lebar_kolom[MAKS_KOLOM];
static int tinggi_baris[MAKS_BARIS];

/* Clipboard */
static char clipboard[MAX_TEXT];
static char clipboard_area[MAKS_BARIS][MAKS_KOLOM][MAX_TEXT];
static int clip_x1 = -1, clip_y1 = -1, clip_x2 = -1, clip_y2 = -1;
static int clip_has_area = 0;

/* Undo/Redo */
static struct op undo_stack[UNDO_MAX];
static struct op redo_stack[UNDO_MAX];
static int undo_top = 0, redo_top = 0;

/* Terminal */
static struct termios simpan_term;
static int mode_raw = 0;

/* Seleksi */
static int selecting = 0;
static int sel_anchor_x = -1, sel_anchor_y = -1;
static int prev_sel_x = -1, prev_sel_y = -1;

/* Status */
static char status_msg[256] = "";

/* Double buffering */
static struct buffer back_buffer;
static int use_double_buffer = 1;

static void update_seleksi_status(const struct konfigurasi *cfg);

/* ============================================================
 * Fungsi Utilitas Buffer
 * ============================================================ */
static int inisialisasi_buffer(struct buffer *buf, size_t kapasitas_awal)
{
    buf->data = malloc(kapasitas_awal);
    if (!buf->data) {
        return -1;
    }
    buf->size = 0;
    buf->capacity = kapasitas_awal;
    return 0;
}

static void bersihkan_buffer(struct buffer *buf)
{
    if (buf->data) {
        free(buf->data);
        buf->data = NULL;
    }
    buf->size = 0;
    buf->capacity = 0;
}

static int perluas_buffer(struct buffer *buf, size_t ukuran_baru)
{
    char *data_baru = realloc(buf->data, ukuran_baru);
    if (!data_baru) {
        return -1;
    }
    buf->data = data_baru;
    buf->capacity = ukuran_baru;
    return 0;
}

static int tulis_buffer(struct buffer *buf, const char *data, size_t panjang)
{
    if (buf->size + panjang > buf->capacity) {
        size_t kapasitas_baru = buf->capacity * 2;
        if (kapasitas_baru < buf->size + panjang) {
            kapasitas_baru = buf->size + panjang + 1024;
        }
        if (perluas_buffer(buf, kapasitas_baru) < 0) {
            return -1;
        }
    }
    memcpy(buf->data + buf->size, data, panjang);
    buf->size += panjang;
    return 0;
}

static void reset_buffer(struct buffer *buf)
{
    buf->size = 0;
}

/* ============================================================
 * Fungsi Utilitas Terminal
 * ============================================================ */
static void pos(int x, int y)
{
    char esc[32];
    int n = snprintf(esc, sizeof(esc), "\033[%d;%dH", y, x);
    if (n > 0) {
        if (use_double_buffer) {
            tulis_buffer(&back_buffer, esc, (size_t)n);
        } else {
            write(STDOUT_FILENO, esc, (size_t)n);
        }
    }
}

static void tulis_teks(const char *teks, size_t panjang)
{
    if (use_double_buffer) {
        tulis_buffer(&back_buffer, teks, panjang);
    } else {
        write(STDOUT_FILENO, teks, panjang);
    }
}

static void flush(void)
{
    if (use_double_buffer) {
        write(STDOUT_FILENO, back_buffer.data, back_buffer.size);
        reset_buffer(&back_buffer);
    } else {
        fflush(stdout);
    }
}

static void masuk_alt(void)
{
    tulis_teks("\033[?1049h\033[?25l", 12);
    if (!use_double_buffer) {
        flush();
    }
}

static void keluar_alt(void)
{
    tulis_teks("\033[?25h\033[?1049l", 12);
    if (!use_double_buffer) {
        flush();
    }
}

static void bersih(void)
{
    tulis_teks(ESC_CLR ESC_HOME, 7);
    if (!use_double_buffer) {
        flush();
    }
}

static void pulihkan_terminal(void)
{
    if (mode_raw) {
        tcsetattr(STDIN_FILENO, TCSANOW, &simpan_term);
        mode_raw = 0;
    }
}

static void tangani_sinyal(int sig)
{
    (void)sig;
    pulihkan_terminal();
    keluar_alt();
    write(STDOUT_FILENO, ESC_CLR ESC_HOME, 7);
    _exit(0);
}

static int inisialisasi_terminal(void)
{
    struct termios t;
    if (tcgetattr(STDIN_FILENO, &simpan_term) == -1) {
        return -1;
    }
    t = simpan_term;
    t.c_lflag &= ~(ECHO | ICANON);
    t.c_cc[VMIN] = 1;
    t.c_cc[VTIME] = 0;
    if (tcsetattr(STDIN_FILENO, TCSANOW, &t) == -1) {
        return -1;
    }
    mode_raw = 1;
    return 0;
}

static int lebar_terminal(void)
{
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == -1) {
        return 80;
    }
    return ws.ws_col;
}

static int tinggi_terminal(void)
{
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == -1) {
        return 24;
    }
    return ws.ws_row;
}

/* ============================================================
 * Fungsi Utilitas Grid
 * ============================================================ */
static void gambar_grid_view(const struct konfigurasi *cfg,
                             int x_awal, int y_awal,
                             int col_start, int col_end,
                             int row_start, int row_end)
{
    int r, c, k, line, y_top = y_awal;
    tulis_teks(FG_DARK, sizeof(FG_DARK) - 1);

    /* Garis atas viewport */
    pos(x_awal, y_awal);
    for (c = col_start; c <= col_end; c++) {
        if (c == col_start) {
            tulis_teks(TL, 3);
        }
        for (k = 0; k < lebar_kolom[c]; k++) {
            tulis_teks(H, 3);
        }
        if (c < col_end) {
            tulis_teks(TC, 3);
        } else {
            tulis_teks(TR, 3);
        }
    }

    /* Body grid */
    for (r = row_start; r <= row_end; r++) {
        int h = tinggi_baris[r];

        /* Isi baris dengan spasi dan garis vertikal */
        for (line = 0; line < h; line++) {
            pos(x_awal, y_top + 1 + line);
            for (c = col_start; c <= col_end; c++) {
                tulis_teks(V, 3);
                for (k = 0; k < lebar_kolom[c]; k++) {
                    tulis_teks(" ", 1);
                }
            }
            tulis_teks(V, 3);
        }

        /* Garis bawah setiap baris */
        pos(x_awal, y_top + h + 1);
        for (c = col_start; c <= col_end; c++) {
            if (r < row_end) {
                if (c == col_start) {
                    tulis_teks(LC, 3);
                }
                for (k = 0; k < lebar_kolom[c]; k++) {
                    tulis_teks(H, 3);
                }
                if (c < col_end) {
                    tulis_teks(CR, 3);
                } else {
                    tulis_teks(RC, 3);
                }
            } else {
                if (c == col_start) {
                    tulis_teks(BL, 3);
                }
                for (k = 0; k < lebar_kolom[c]; k++) {
                    tulis_teks(H, 3);
                }
                if (c < col_end) {
                    tulis_teks(BC, 3);
                } else {
                    tulis_teks(BR, 3);
                }
            }
        }
        y_top += h + 1;
    }

    tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);
}

/* ============================================================
 * Fungsi Utilitas Sel
 * ============================================================ */
static void gambar_isi_sel_view(const struct konfigurasi *cfg,
                                int x_awal, int y_awal,
                                int col_start, int row_start,
                                int c, int r)
{
    const char *teks = isi[r][c];
    int w, h, x0, y0, i, line;
    int len = (int)strlen(teks), start = 0;

    /* Hitung posisi sel */
    x0 = x_awal + 1;
    y0 = y_awal;
    for (i = col_start; i < c; i++) {
        x0 += lebar_kolom[i] + 1;
    }
    for (i = row_start; i < r; i++) {
        y0 += tinggi_baris[i] + 1;
    }
    w = lebar_kolom[c];
    h = tinggi_baris[r];

    /* Gambar teks dengan autowrap */
    for (line = 0; line < h; line++) {
        int remaining = len - start;
        int take = remaining > w ? w : remaining;
        int offset = 0;
        pos(x0, y0 + 1 + line);
        for (i = 0; i < w; i++) {
            tulis_teks(" ", 1);
        }
        if (take <= 0) {
            continue;
        }
        if (align_sel[r][c] == CENTER) {
            offset = (w - take) / 2;
        } else if (align_sel[r][c] == RIGHT) {
            offset = (w - take);
        }
        if (offset < 0) {
            offset = 0;
        }
        pos(x0 + offset, y0 + 1 + line);
        tulis_teks(teks + start, (size_t)take);
        start += take;
        if (start >= len) {
            break;
        }
    }
    if (len - start > 0 && h > 0 && w > 0) {
        pos(x0 + w - 1, y0 + h);
        tulis_teks("…", 3);
    }
}

/* ============================================================
 * Fungsi Utilitas UI
 * ============================================================ */
static void gambar_topbar(const struct konfigurasi *cfg)
{
    int cols = lebar_terminal();
    char judul[] = "TABEL v0.7";
    char label[512];
    char kol = (char)('A' + cfg->aktif_x);
    int bar = cfg->aktif_y + 1;

    /* Background gelap untuk top bar */
    pos(1, 1);
    tulis_teks(BG_DARK, sizeof(BG_DARK) - 1);
    {
        int i;
        for (i = 0; i < cols; i++) {
            tulis_teks(" ", 1);
        }
    }

    if (isi[cfg->aktif_y][cfg->aktif_x][0] == '\0') {
        snprintf(label, sizeof(label), "kolom %c%d:", kol, bar);
    } else {
        snprintf(label, sizeof(label), "kolom %c%d: %s", kol, bar,
                 isi[cfg->aktif_y][cfg->aktif_x]);
    }

    pos(2, 1);
    tulis_teks(FG_WHITE, sizeof(FG_WHITE) - 1);
    tulis_teks(label, strlen(label));
    pos(cols - (int)strlen(judul) - 1, 1);
    tulis_teks(FG_GRAY, sizeof(FG_GRAY) - 1);
    tulis_teks(judul, strlen(judul));
    tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);
}

static void gambar_statusbar(const struct konfigurasi *cfg)
{
    int cols = lebar_terminal(), rows = tinggi_terminal(), y = rows;
    char info[128];
    snprintf(info, sizeof(info), "lebar: %d tinggi: %d  [?]: bantuan",
             lebar_kolom[cfg->aktif_x], tinggi_baris[cfg->aktif_y]);
    
    /* Background gelap untuk status bar */
    pos(1, y);
    tulis_teks(BG_DARK, sizeof(BG_DARK) - 1);
    {
        int i;
        for (i = 0; i < cols; i++) {
            tulis_teks(" ", 1);
        }
    }
    
    pos(2, y);
    tulis_teks(FG_WHITE, sizeof(FG_WHITE) - 1);
    tulis_teks(status_msg, strlen(status_msg));
    pos(cols - (int)strlen(info) - 1, y);
    tulis_teks(FG_GRAY, sizeof(FG_GRAY) - 1);
    tulis_teks(info, strlen(info));
    tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);
}

static void gambar_label_kolom(const struct konfigurasi *cfg,
                               int x_awal, int col_start, int col_end)
{
    int x = x_awal + 1, c, term_w = lebar_terminal();
    pos(1, 2);
    {
        int i;
        for (i = 0; i < term_w; i++) {
            tulis_teks(" ", 1);
        }
    }
    for (c = col_start; c <= col_end; c++) {
        char ch = (char)('A' + c);
        pos(x + lebar_kolom[c] / 2, 2);
        tulis_teks(&ch, 1);
        x += lebar_kolom[c] + 1;
    }
}

static void gambar_nomor_baris(const struct konfigurasi *cfg,
                                int y_awal, int row_start, int row_end)
{
    int y = y_awal, r;
    for (r = row_start; r <= row_end; r++) {
        int i;
        pos(1, y + 1);
        for (i = 0; i < 4; i++) {
            tulis_teks(" ", 1);
        }
        y += tinggi_baris[r] + 1;
    }
    y = y_awal;
    for (r = row_start; r <= row_end; r++) {
        char num[8];
        snprintf(num, sizeof(num), "%2d", r + 1);
        pos(2, y + 1);
        tulis_teks(num, strlen(num));
        y += tinggi_baris[r] + 1;
    }
}

/* ============================================================
 * Fungsi Utilitas Viewport
 * ============================================================ */
static void hitung_viewport(const struct konfigurasi *cfg,
                            int *x_awal, int *y_awal,
                            int *pad_left, int *vis_w, int *vis_h,
                            int *col_start, int *col_end,
                            int *row_start, int *row_end)
{
    int term_w = lebar_terminal();
    int term_h = tinggi_terminal();
    int grid_top = 3;
    int status_bar_rows = 1;
    int available_h = term_h - grid_top - status_bar_rows;
    int padL = 5;
    int available_w = term_w - padL;
    int x = 0, c, start;
    int y = 0, r;
    
    /* Validasi input */
    if (!cfg || !x_awal || !y_awal || !pad_left || !vis_w || !vis_h ||
        !col_start || !col_end || !row_start || !row_end) {
        return;
    }
    
    if (available_h < 1) {
        available_h = 1;
    }
    
    if (available_w < 8) {
        available_w = 8;
    }

    *x_awal = padL;
    *y_awal = grid_top;
    *pad_left = padL;
    *vis_w = available_w;
    *vis_h = available_h;

    /* kolom terlihat */
    x = 0;
    c = cfg->view_col;
    start = c;
    while (c < cfg->kolom) {
        int w = lebar_kolom[c] + 1;
        if (x + w > available_w) {
            break;
        }
        x += w;
        c++;
    }
    if (c == start && c < cfg->kolom) {
        c++;
    }
    *col_start = start;
    *col_end = c - 1;
    
    /* baris terlihat */
    y = 0;
    r = cfg->view_row;
    start = r;
    while (r < cfg->baris) {
        int h = tinggi_baris[r] + 1;
        if (y + h > available_h) {
            break;
        }
        y += h;
        r++;
    }
    if (r == start && r < cfg->baris) {
        r++;
    }
    *row_start = start;
    *row_end = r - 1;
}

/* ============================================================
 * Fungsi Utilitas Seleksi
 * ============================================================ */
static void gambar_area_hijau_view(const struct konfigurasi *cfg,
                                   int x_awal, int y_awal,
                                   int col_start, int col_end,
                                   int row_start, int row_end,
                                   int x1, int y1, int x2, int y2)
{
    int minx = x1 < x2 ? x1 : x2, maxx = x1 > x2 ? x1 : x2;
    int miny = y1 < y2 ? y1 : y2, maxy = y1 > y2 ? y1 : y2;
    int cs = minx < col_start ? col_start : minx;
    int ce = maxx > col_end ? col_end : maxx;
    int rs = miny < row_start ? row_start : miny;
    int re = maxy > row_end ? row_end : maxy;
    int r, c, k, line, y_top, r0;
    
    if (cs > ce || rs > re) {
        return;
    }

    tulis_teks(FG_GREEN, sizeof(FG_GREEN) - 1);
    y_top = y_awal;
    for (r0 = row_start; r0 < rs; r0++) {
        y_top += tinggi_baris[r0] + 1;
    }

    /* top border */
    {
        int c0;
        int x = x_awal;
        for (c0 = col_start; c0 < cs; c0++) {
            x += lebar_kolom[c0] + 1;
        }
        pos(x, y_top);
        for (c = cs; c <= ce; c++) {
            if (c == cs) {
                tulis_teks(TL, 3);
            }
            for (k = 0; k < lebar_kolom[c]; k++) {
                tulis_teks(H, 3);
            }
            if (c < ce) {
                tulis_teks(TC, 3);
            } else {
                tulis_teks(TR, 3);
            }
        }
    }

    /* body + interior sides */
    {
        int y = y_top;
        for (r = rs; r <= re; r++) {
            int h = tinggi_baris[r];
            int x_start = x_awal, c0;
            for (c0 = col_start; c0 < cs; c0++) {
                x_start += lebar_kolom[c0] + 1;
            }
            for (line = 0; line < h; line++) {
                pos(x_start, y + 1 + line);
                for (c = cs; c <= ce; c++) {
                    tulis_teks(V, 3);
                    for (k = 0; k < lebar_kolom[c]; k++) {
                        tulis_teks(" ", 1);
                    }
                }
                tulis_teks(V, 3);
            }
            pos(x_start, y + h + 1);
            for (c = cs; c <= ce; c++) {
                if (r < re) {
                    if (c == cs) {
                        tulis_teks(LC, 3);
                    }
                    for (k = 0; k < lebar_kolom[c]; k++) {
                        tulis_teks(H, 3);
                    }
                    if (c < ce) {
                        tulis_teks(CR, 3);
                    } else {
                        tulis_teks(RC, 3);
                    }
                } else {
                    if (c == cs) {
                        tulis_teks(BL, 3);
                    }
                    for (k = 0; k < lebar_kolom[c]; k++) {
                        tulis_teks(H, 3);
                    }
                    if (c < ce) {
                        tulis_teks(BC, 3);
                    } else {
                        tulis_teks(BR, 3);
                    }
                }
            }
            y += h + 1;
        }
    }
    tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);

    for (r = rs; r <= re; r++) {
        for (c = cs; c <= ce; c++) {
            if (isi[r][c][0] != '\0') {
                gambar_isi_sel_view(cfg, x_awal, y_awal, col_start, row_start, c, r);
            }
        }
    }
}

static void gambar_seleksi_cyan_view(const struct konfigurasi *cfg,
                                     int x_awal, int y_awal,
                                     int col_start, int col_end,
                                     int row_start, int row_end,
                                     int ax, int ay, int bx, int by)
{
    int minx = ax < bx ? ax : bx, maxx = ax > bx ? ax : bx;
    int miny = ay < by ? ay : by, maxy = ay > by ? ay : by;
    int vx1 = minx < col_start ? col_start : minx;
    int vx2 = maxx > col_end ? col_end : maxx;
    int vy1 = miny < row_start ? row_start : miny;
    int vy2 = maxy > row_end ? row_end : maxy;
    int i, x0 = x_awal + 1, y0 = y_awal, total_w = 0, total_h = 0;
    
    if (vx1 > vx2 || vy1 > vy2) {
        return;
    }

    for (i = col_start; i < vx1; i++) {
        x0 += lebar_kolom[i] + 1;
    }
    for (i = row_start; i < vy1; i++) {
        y0 += tinggi_baris[i] + 1;
    }
    for (i = vx1; i <= vx2; i++) {
        total_w += lebar_kolom[i] + 1;
    }
    for (i = vy1; i <= vy2; i++) {
        total_h += tinggi_baris[i] + 1;
    }

    tulis_teks(FG_CYAN, sizeof(FG_CYAN) - 1);
    pos(x0 - 1, y0);
    tulis_teks(TL, 3);
    for (i = 0; i < total_w - 1; i++) {
        tulis_teks(H, 3);
    }
    tulis_teks(TR, 3);
    pos(x0 - 1, y0 + total_h);
    tulis_teks(BL, 3);
    for (i = 0; i < total_w - 1; i++) {
        tulis_teks(H, 3);
    }
    tulis_teks(BR, 3);
    for (i = 1; i < total_h; i++) {
        pos(x0 - 1, y0 + i);
        tulis_teks(V, 3);
        pos(x0 + total_w - 1, y0 + i);
        tulis_teks(V, 3);
    }
    tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);
}

/* ============================================================
 * Fungsi Utilitas Sel Aktif
 * ============================================================ */
static void gambar_sel_aktif_view(const struct konfigurasi *cfg,
                                  int x_awal, int y_awal,
                                  int col_start, int col_end,
                                  int row_start, int row_end)
{
    int ax = cfg->aktif_x, ay = cfg->aktif_y;
    int w, h, x0, y0, k, line;
    
    if (ax < col_start || ax > col_end || ay < row_start || ay > row_end) {
        return;
    }

    /* Sel normal */
    x0 = x_awal + 1;
    y0 = y_awal;
    for (k = col_start; k < ax; k++) {
        x0 += lebar_kolom[k] + 1;
    }
    for (k = row_start; k < ay; k++) {
        y0 += tinggi_baris[k] + 1;
    }
    w = lebar_kolom[ax];
    h = tinggi_baris[ay];

    tulis_teks(FG_WHITE, sizeof(FG_WHITE) - 1);
    pos(x0 - 1, y0);
    tulis_teks(TL, 3);
    for (k = 0; k < w; k++) {
        tulis_teks(H, 3);
    }
    tulis_teks(TR, 3);
    for (line = 0; line < h; line++) {
        pos(x0 - 1, y0 + 1 + line);
        tulis_teks(V, 3);
        pos(x0 + w, y0 + 1 + line);
        tulis_teks(V, 3);
    }
    pos(x0 - 1, y0 + h + 1);
    tulis_teks(BL, 3);
    for (k = 0; k < w; k++) {
        tulis_teks(H, 3);
    }
    tulis_teks(BR, 3);
    tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);
}

/* ============================================================
 * Fungsi Render
 * ============================================================ */
static void gambar_semua_isi_view(const struct konfigurasi *cfg,
                                  int x_awal, int y_awal,
                                  int col_start, int col_end,
                                  int row_start, int row_end)
{
    int r, c;
    for (r = row_start; r <= row_end; r++) {
        for (c = col_start; c <= col_end; c++) {
            if (isi[r][c][0] != '\0') {
                gambar_isi_sel_view(cfg, x_awal, y_awal, col_start, row_start, c, r);
            }
        }
    }
}

static void render(const struct konfigurasi *cfg)
{
    int x_awal, y_awal, pad_left, vis_w, vis_h;
    int col_start, col_end, row_start, row_end;
    
    bersih();
    gambar_topbar(cfg);
    hitung_viewport(cfg, &x_awal, &y_awal, &pad_left, &vis_w, &vis_h,
                    &col_start, &col_end, &row_start, &row_end);
    gambar_label_kolom(cfg, x_awal, col_start, col_end);
    gambar_grid_view(cfg, x_awal, y_awal, col_start, col_end, row_start, row_end);
    gambar_nomor_baris(cfg, y_awal, row_start, row_end);
    gambar_semua_isi_view(cfg, x_awal, y_awal, col_start, col_end, row_start, row_end);
    if (clip_has_area) {
        gambar_area_hijau_view(cfg, x_awal, y_awal, col_start, col_end,
                               row_start, row_end, clip_x1, clip_y1, clip_x2, clip_y2);
    }
    if (selecting) {
        gambar_seleksi_cyan_view(cfg, x_awal, y_awal, col_start, col_end,
                                 row_start, row_end, sel_anchor_x, sel_anchor_y,
                                 cfg->aktif_x, cfg->aktif_y);
    }
    gambar_sel_aktif_view(cfg, x_awal, y_awal, col_start, col_end, row_start, row_end);
    gambar_statusbar(cfg);
    pos(1, 1);
    tulis_teks("\033[?25l", 6);
    flush();
}

/* Redraw parsial untuk navigasi */
/* ============================================================
 * Fungsi Redraw Parsial yang Dioptimalkan (Versi Sempurna)
 * ============================================================ */
static void redraw_navigasi_parsial(const struct konfigurasi *cfg)
{
    int x_awal, y_awal, pad_left, vis_w, vis_h;
    int col_start, col_end, row_start, row_end;
    
    /* Hitung viewport saat ini */
    hitung_viewport(cfg, &x_awal, &y_awal, &pad_left, &vis_w, &vis_h,
                    &col_start, &col_end, &row_start, &row_end);
    
    /* Hapus highlight sel sebelumnya */
    if (cfg->prev_x >= col_start && cfg->prev_x <= col_end &&
        cfg->prev_y >= row_start && cfg->prev_y <= row_end) {
        int w, h, x0, y0, k, line;
        x0 = x_awal + 1;
        y0 = y_awal;
        for (k = col_start; k < cfg->prev_x; k++) {
            x0 += lebar_kolom[k] + 1;
        }
        for (k = row_start; k < cfg->prev_y; k++) {
            y0 += tinggi_baris[k] + 1;
        }
        w = lebar_kolom[cfg->prev_x];
        h = tinggi_baris[cfg->prev_y];
        
        /* Gambar ulang grid di sekitar sel sebelumnya dengan benar */
        /* Atas */
        pos(x0 - 1, y0);
        tulis_teks(FG_DARK, sizeof(FG_DARK) - 1);
        
        /* Tentukan karakter kiri atas */
        if (cfg->prev_y == row_start) {
            if (cfg->prev_x == col_start) {
                tulis_teks(TL, 3);  /* Sudut kiri atas viewport */
            } else {
                tulis_teks(TC, 3);  /* Tengah atas */
            }
        } else {
            if (cfg->prev_x == col_start) {
                tulis_teks(LC, 3);  /* Tengah kiri */
            } else {
                tulis_teks(CR, 3);  /* Persimpangan */
            }
        }
        
        /* Garis horizontal atas */
        for (k = 0; k < w; k++) {
            tulis_teks(H, 3);
        }
        
        /* Tentukan karakter kanan atas */
        if (cfg->prev_y == row_start) {
            if (cfg->prev_x == col_end) {
                tulis_teks(TR, 3);  /* Sudut kanan atas viewport */
            } else {
                tulis_teks(TC, 3);  /* Tengah atas */
            }
        } else {
            if (cfg->prev_x == col_end) {
                tulis_teks(RC, 3);  /* Tengah kanan */
            } else {
                tulis_teks(CR, 3);  /* Persimpangan */
            }
        }
        
        /* Samping kiri dan kanan */
        for (line = 0; line < h; line++) {
            pos(x0 - 1, y0 + 1 + line);
            tulis_teks(V, 3);
            pos(x0 + w, y0 + 1 + line);
            tulis_teks(V, 3);
        }
        
        /* Bawah */
        pos(x0 - 1, y0 + h + 1);
        
        /* Tentukan karakter kiri bawah */
        if (cfg->prev_y == row_end) {
            if (cfg->prev_x == col_start) {
                tulis_teks(BL, 3);  /* Sudut kiri bawah viewport */
            } else {
                tulis_teks(BC, 3);  /* Tengah bawah */
            }
        } else {
            if (cfg->prev_x == col_start) {
                tulis_teks(LC, 3);  /* Tengah kiri */
            } else {
                tulis_teks(CR, 3);  /* Persimpangan */
            }
        }
        
        /* Garis horizontal bawah */
        for (k = 0; k < w; k++) {
            tulis_teks(H, 3);
        }
        
        /* Tentukan karakter kanan bawah */
        if (cfg->prev_y == row_end) {
            if (cfg->prev_x == col_end) {
                tulis_teks(BR, 3);  /* Sudut kanan bawah viewport */
            } else {
                tulis_teks(BC, 3);  /* Tengah bawah */
            }
        } else {
            if (cfg->prev_x == col_end) {
                tulis_teks(RC, 3);  /* Tengah kanan */
            } else {
                tulis_teks(CR, 3);  /* Persimpangan */
            }
        }
        
        tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);
        
        /* Gambar kembali isi sel */
        if (isi[cfg->prev_y][cfg->prev_x][0] != '\0') {
            gambar_isi_sel_view(cfg, x_awal, y_awal, col_start, row_start,
                                cfg->prev_x, cfg->prev_y);
        }
    }
    
    /* Gambar area hijau jika ada */
    if (clip_has_area) {
        gambar_area_hijau_view(cfg, x_awal, y_awal, col_start, col_end,
                               row_start, row_end, clip_x1, clip_y1, clip_x2, clip_y2);
    }
    
    /* Gambar highlight sel aktif */
    gambar_sel_aktif_view(cfg, x_awal, y_awal, col_start, col_end, row_start, row_end);
    
    /* Update topbar dan statusbar */
    gambar_topbar(cfg);
    gambar_statusbar(cfg);
    
    pos(1, 1);
    tulis_teks("\033[?25l", 6);
    flush();
}

/* Redraw parsial untuk seleksi */
static void redraw_seleksi_parsial(const struct konfigurasi *cfg)
{
    int x_awal, y_awal, pad_left, vis_w, vis_h;
    int col_start, col_end, row_start, row_end;
    
    /* Hitung viewport saat ini */
    hitung_viewport(cfg, &x_awal, &y_awal, &pad_left, &vis_w, &vis_h,
                    &col_start, &col_end, &row_start, &row_end);
    
    /* Hapus seleksi sebelumnya jika ada */
    if (prev_sel_x >= 0 && prev_sel_y >= 0) {
        int minx = sel_anchor_x < prev_sel_x ? sel_anchor_x : prev_sel_x;
        int maxx = sel_anchor_x > prev_sel_x ? sel_anchor_x : prev_sel_x;
        int miny = sel_anchor_y < prev_sel_y ? sel_anchor_y : prev_sel_y;
        int maxy = sel_anchor_y > prev_sel_y ? sel_anchor_y : prev_sel_y;
        
        int cs = minx < col_start ? col_start : minx;
        int ce = maxx > col_end ? col_end : maxx;
        int rs = miny < row_start ? row_start : miny;
        int re = maxy > row_end ? row_end : maxy;
        
        if (cs <= ce && rs <= re) {
            int r, c;
            for (r = rs; r <= re; r++) {
                for (c = cs; c <= ce; c++) {
                    /* Gambar kembali grid normal */
                    int w, h, x0, y0, k, line;
                    x0 = x_awal + 1;
                    y0 = y_awal;
                    for (k = col_start; k < c; k++) {
                        x0 += lebar_kolom[k] + 1;
                    }
                    for (k = row_start; k < r; k++) {
                        y0 += tinggi_baris[k] + 1;
                    }
                    w = lebar_kolom[c];
                    h = tinggi_baris[r];
                    
                    /* Gambar border normal */
                    tulis_teks(FG_DARK, sizeof(FG_DARK) - 1);
                    pos(x0 - 1, y0);
                    
                    /* Tentukan karakter kiri atas */
                    if (r == row_start) {
                        if (c == col_start) {
                            tulis_teks(TL, 3);  /* Sudut kiri atas viewport */
                        } else {
                            tulis_teks(TC, 3);  /* Tengah atas */
                        }
                    } else {
                        if (c == col_start) {
                            tulis_teks(LC, 3);  /* Tengah kiri */
                        } else {
                            tulis_teks(CR, 3);  /* Persimpangan */
                        }
                    }
                    
                    /* Garis horizontal atas */
                    for (k = 0; k < w; k++) {
                        tulis_teks(H, 3);
                    }
                    
                    /* Tentukan karakter kanan atas */
                    if (r == row_start) {
                        if (c == col_end) {
                            tulis_teks(TR, 3);  /* Sudut kanan atas viewport */
                        } else {
                            tulis_teks(TC, 3);  /* Tengah atas */
                        }
                    } else {
                        if (c == col_end) {
                            tulis_teks(RC, 3);  /* Tengah kanan */
                        } else {
                            tulis_teks(CR, 3);  /* Persimpangan */
                        }
                    }
                    
                    /* Samping kiri dan kanan */
                    for (line = 0; line < h; line++) {
                        pos(x0 - 1, y0 + 1 + line);
                        tulis_teks(V, 3);
                        pos(x0 + w, y0 + 1 + line);
                        tulis_teks(V, 3);
                    }
                    
                    /* Bawah */
                    pos(x0 - 1, y0 + h + 1);
                    
                    /* Tentukan karakter kiri bawah */
                    if (r == row_end) {
                        if (c == col_start) {
                            tulis_teks(BL, 3);  /* Sudut kiri bawah viewport */
                        } else {
                            tulis_teks(BC, 3);  /* Tengah bawah */
                        }
                    } else {
                        if (c == col_start) {
                            tulis_teks(LC, 3);  /* Tengah kiri */
                        } else {
                            tulis_teks(CR, 3);  /* Persimpangan */
                        }
                    }
                    
                    /* Garis horizontal bawah */
                    for (k = 0; k < w; k++) {
                        tulis_teks(H, 3);
                    }
                    
                    /* Tentukan karakter kanan bawah */
                    if (r == row_end) {
                        if (c == col_end) {
                            tulis_teks(BR, 3);  /* Sudut kanan bawah viewport */
                        } else {
                            tulis_teks(BC, 3);  /* Tengah bawah */
                        }
                    } else {
                        if (c == col_end) {
                            tulis_teks(RC, 3);  /* Tengah kanan */
                        } else {
                            tulis_teks(CR, 3);  /* Persimpangan */
                        }
                    }
                    
                    tulis_teks(ESC_NORM, sizeof(ESC_NORM) - 1);
                    
                    /* Gambar kembali isi sel */
                    if (isi[r][c][0] != '\0') {
                        gambar_isi_sel_view(cfg, x_awal, y_awal, col_start, row_start, c, r);
                    }
                }
            }
        }
    }
    
    /* Simpan posisi seleksi saat ini */
    prev_sel_x = cfg->aktif_x;
    prev_sel_y = cfg->aktif_y;
    
    /* Gambar area hijau jika ada */
    if (clip_has_area) {
        gambar_area_hijau_view(cfg, x_awal, y_awal, col_start, col_end,
                               row_start, row_end, clip_x1, clip_y1, clip_x2, clip_y2);
    }
    
    /* Gambar seleksi baru jika sedang seleksi */
    if (selecting) {
        gambar_seleksi_cyan_view(cfg, x_awal, y_awal, col_start, col_end,
                                 row_start, row_end, sel_anchor_x, sel_anchor_y,
                                 cfg->aktif_x, cfg->aktif_y);
    }
    
    /* Gambar highlight sel aktif */
    gambar_sel_aktif_view(cfg, x_awal, y_awal, col_start, col_end, row_start, row_end);
    
    /* Update topbar dan statusbar */
    gambar_topbar(cfg);
    gambar_statusbar(cfg);
    
    pos(1, 1);
    tulis_teks("\033[?25l", 6);
    flush();
}

/* ============================================================
 * Fungsi Undo/Redo
 * ============================================================ */
static void push_undo(int x, int y, const char *before, const char *after)
{
    if (undo_top >= UNDO_MAX) {
        undo_top = UNDO_MAX - 1;
    }
    undo_stack[undo_top].x = x;
    undo_stack[undo_top].y = y;
    strncpy(undo_stack[undo_top].before, before, MAX_TEXT - 1);
    strncpy(undo_stack[undo_top].after, after, MAX_TEXT - 1);
    undo_stack[undo_top].before[MAX_TEXT - 1] = '\0';
    undo_stack[undo_top].after[MAX_TEXT - 1] = '\0';
    undo_top++;
    redo_top = 0;
}

static void set_cell_text(struct konfigurasi *cfg, int x, int y,
                          const char *text, int record_undo)
{
    char before[MAX_TEXT];
    strncpy(before, isi[y][x], MAX_TEXT - 1);
    before[MAX_TEXT - 1] = '\0';
    strncpy(isi[y][x], text, MAX_TEXT - 1);
    isi[y][x][MAX_TEXT - 1] = '\0';
    if (record_undo) {
        push_undo(x, y, before, isi[y][x]);
    }
}

/* ============================================================
 * Fungsi Navigasi
 * ============================================================ */
static void move_right(struct konfigurasi *cfg)
{
    if (cfg->aktif_x < cfg->kolom - 1) {
        cfg->prev_x = cfg->aktif_x;
        cfg->prev_y = cfg->aktif_y;
        cfg->aktif_x++;
        
        /* Cek apakah perlu menggeser viewport */
        int xa, ya, pad, vw, vh, cs, ce, rs, re;
        hitung_viewport(cfg, &xa, &ya, &pad, &vw, &vh, &cs, &ce, &rs, &re);
        
        /* Jika sedang seleksi, update status message dan redraw parsial */
        if (selecting) {
            update_seleksi_status(cfg);
            redraw_seleksi_parsial(cfg);
        } else {
            /* Jika sel aktif masih dalam viewport yang sama, gunakan redraw parsial */
            if (cfg->aktif_x >= cs && cfg->aktif_x <= ce) {
                redraw_navigasi_parsial(cfg);
            } else {
                /* Jika tidak, perlu menggeser viewport dan render penuh */
                cfg->view_col = cfg->aktif_x;
                render(cfg);
            }
        }
    }
}

static void move_left(struct konfigurasi *cfg)
{
    if (cfg->aktif_x > 0) {
        cfg->prev_x = cfg->aktif_x;
        cfg->prev_y = cfg->aktif_y;
        cfg->aktif_x--;
        
        /* Cek apakah perlu menggeser viewport */
        int xa, ya, pad, vw, vh, cs, ce, rs, re;
        hitung_viewport(cfg, &xa, &ya, &pad, &vw, &vh, &cs, &ce, &rs, &re);
        
        /* Jika sedang seleksi, update status message dan redraw parsial */
        if (selecting) {
            update_seleksi_status(cfg);
            redraw_seleksi_parsial(cfg);
        } else {
            /* Jika sel aktif masih dalam viewport yang sama, gunakan redraw parsial */
            if (cfg->aktif_x >= cs && cfg->aktif_x <= ce) {
                redraw_navigasi_parsial(cfg);
            } else {
                /* Jika tidak, perlu menggeser viewport dan render penuh */
                cfg->view_col = cfg->aktif_x;
                render(cfg);
            }
        }
    }
}

static void move_down(struct konfigurasi *cfg)
{
    if (cfg->aktif_y < cfg->baris - 1) {
        cfg->prev_x = cfg->aktif_x;
        cfg->prev_y = cfg->aktif_y;
        cfg->aktif_y++;
        
        /* Cek apakah perlu menggeser viewport */
        int xa, ya, pad, vw, vh, cs, ce, rs, re;
        hitung_viewport(cfg, &xa, &ya, &pad, &vw, &vh, &cs, &ce, &rs, &re);
        
        /* Jika sedang seleksi, update status message dan redraw parsial */
        if (selecting) {
            update_seleksi_status(cfg);
            redraw_seleksi_parsial(cfg);
        } else {
            /* Jika sel aktif masih dalam viewport yang sama, gunakan redraw parsial */
            if (cfg->aktif_y >= rs && cfg->aktif_y <= re) {
                redraw_navigasi_parsial(cfg);
            } else {
                /* Jika tidak, perlu menggeser viewport dan render penuh */
                cfg->view_row = cfg->aktif_y;
                render(cfg);
            }
        }
    }
}

static void move_up(struct konfigurasi *cfg)
{
    if (cfg->aktif_y > 0) {
        cfg->prev_x = cfg->aktif_x;
        cfg->prev_y = cfg->aktif_y;
        cfg->aktif_y--;
        
        /* Cek apakah perlu menggeser viewport */
        int xa, ya, pad, vw, vh, cs, ce, rs, re;
        hitung_viewport(cfg, &xa, &ya, &pad, &vw, &vh, &cs, &ce, &rs, &re);
        
        /* Jika sedang seleksi, update status message dan redraw parsial */
        if (selecting) {
            update_seleksi_status(cfg);
            redraw_seleksi_parsial(cfg);
        } else {
            /* Jika sel aktif masih dalam viewport yang sama, gunakan redraw parsial */
            if (cfg->aktif_y >= rs && cfg->aktif_y <= re) {
                redraw_navigasi_parsial(cfg);
            } else {
                /* Jika tidak, perlu menggeser viewport dan render penuh */
                cfg->view_row = cfg->aktif_y;
                render(cfg);
            }
        }
    }
}

static void ensure_active_visible(struct konfigurasi *cfg)
{
    int xa, ya, pad, vw, vh, cs, ce, rs, re;
    hitung_viewport(cfg, &xa, &ya, &pad, &vw, &vh, &cs, &ce, &rs, &re);
    
    /* Geser viewport satu kolom/baris saat ini jika perlu */
    if (cfg->aktif_x < cs) {
        cfg->view_col = cfg->aktif_x;
    } else if (cfg->aktif_x > ce) {
        cfg->view_col = cfg->aktif_x;
    }
    
    if (cfg->aktif_y < rs) {
        cfg->view_row = cfg->aktif_y;
    } else if (cfg->aktif_y > re) {
        cfg->view_row = cfg->aktif_y;
    }
}

/* ============================================================
 * Fungsi Mode Edit
 * ============================================================ */
static void mode_edit(struct konfigurasi *cfg)
{
    char buf[MAX_TEXT];
    int len, cursor;
    unsigned char ch;
    char kol = (char)('A' + cfg->aktif_x);
    int bar = cfg->aktif_y + 1;
    char label[64];
    int input_x;

    strncpy(buf, isi[cfg->aktif_y][cfg->aktif_x], MAX_TEXT - 1);
    buf[MAX_TEXT - 1] = '\0';
    len = (int)strlen(buf);
    cursor = len;
    snprintf(label, sizeof(label), "kolom %c%d: ", kol, bar);
    input_x = 2 + (int)strlen(label);

    /* Tampilkan label + isi lama */
    pos(1, 1);
    {
        int i;
        for (i = 0; i < lebar_terminal(); i++) {
            tulis_teks(" ", 1);
        }
    }
    pos(2, 1);
    tulis_teks(label, strlen(label));
    tulis_teks(buf, (size_t)len);
    {
        char judul[] = "TABEL v0.7";
        pos(lebar_terminal() - (int)strlen(judul) - 1, 1);
        tulis_teks(judul, strlen(judul));
    }
    pos(input_x + cursor, 1);
    tulis_teks("\033[?25h", 6);
    flush();

    while (read(STDIN_FILENO, &ch, 1) > 0) {
        if (ch == '\n' || ch == '\r') {
            set_cell_text(cfg, cfg->aktif_x, cfg->aktif_y, buf, 1);
            snprintf(status_msg, sizeof(status_msg), "Mengubah isi kolom %c%d", kol, bar);
            break;
        } else if (ch == '\t') {
            set_cell_text(cfg, cfg->aktif_x, cfg->aktif_y, buf, 1);
            move_right(cfg);
            ensure_active_visible(cfg);
            render(cfg);
            /* Lanjut ke sel berikutnya */
            mode_edit(cfg);
            return;
        } else if (ch == 0x1B) {
            unsigned char s1;
            if (read(STDIN_FILENO, &s1, 1) <= 0) {
                continue;
            }
            if (s1 == '[') {
                unsigned char s2;
                if (read(STDIN_FILENO, &s2, 1) <= 0) {
                    continue;
                }
                if (s2 == 'D') {
                    if (cursor > 0) {
                        cursor--;
                    }
                } else if (s2 == 'C') {
                    if (cursor < len) {
                        cursor++;
                    }
                } else if (s2 == '3') {
                    unsigned char t;
                    if (read(STDIN_FILENO, &t, 1) <= 0) {
                        continue;
                    }
                    if (t == '~') {
                        if (cursor < len) {
                            memmove(buf + cursor, buf + cursor + 1,
                                    (size_t)(len - cursor));
                            len--;
                        }
                    }
                }
            }
        } else if (ch == 0x7F) {
            if (cursor > 0) {
                memmove(buf + cursor - 1, buf + cursor,
                        (size_t)(len - (cursor - 1)));
                cursor--;
                len--;
            }
        } else if (ch >= 0x20 && ch <= 0x7E) {
            if (len < MAX_TEXT - 1) {
                memmove(buf + cursor + 1, buf + cursor,
                        (size_t)(len - cursor));
                buf[cursor] = (char)ch;
                cursor++;
                len++;
                buf[len] = '\0';
            }
        }

        /* Update tampilan */
        pos(1, 1);
        {
            int i;
            for (i = 0; i < lebar_terminal(); i++) {
                tulis_teks(" ", 1);
            }
        }
        pos(2, 1);
        tulis_teks(label, strlen(label));
        tulis_teks(buf, (size_t)len);
        {
            char judul[] = "TABEL v0.7";
            pos(lebar_terminal() - (int)strlen(judul) - 1, 1);
            tulis_teks(judul, strlen(judul));
        }
        pos(input_x + cursor, 1);
        flush();
    }

    tulis_teks("\033[?25l", 6);
    render(cfg);
}

/* ============================================================
 * Fungsi Command Line
 * ============================================================ */
static int evaluasi_formula(const char *formula, double *hasil)
{
    /* Implementasi sederhana untuk evaluasi formula */
    /* Contoh: :SUM A1-A8 atau :AVG A1-D4 */
    char formula_copy[MAX_FORMULA_LENGTH];
    char *token;
    char fungsi[16];
    int x1, y1, x2, y2;
    double total = 0.0;
    int count = 0;
    int y;

    if (formula[0] != ':') {
        return -1;
    }

    strncpy(formula_copy, formula, MAX_FORMULA_LENGTH - 1);
    formula_copy[MAX_FORMULA_LENGTH - 1] = '\0';

    token = strtok(formula_copy + 1, " ");
    if (!token) {
        return -1;
    }

    strncpy(fungsi, token, sizeof(fungsi) - 1);
    fungsi[sizeof(fungsi) - 1] = '\0';

    token = strtok(NULL, " ");
    if (!token) {
        return -1;
    }

    /* Parse koordinat pertama */
    if (token[0] >= 'A' && token[0] <= 'Z') {
        x1 = token[0] - 'A';
        y1 = atoi(token + 1) - 1;
    } else {
        return -1;
    }

    token = strtok(NULL, " ");
    if (!token) {
        /* Hanya satu sel */
        if (isi[y1][x1][0] != '\0') {
            *hasil = atof(isi[y1][x1]);
        } else {
            *hasil = 0.0;
        }
        return 0;
    }

    /* Parse koordinat kedua */
    if (token[0] >= 'A' && token[0] <= 'Z') {
        x2 = token[0] - 'A';
        y2 = atoi(token + 1) - 1;
    } else {
        return -1;
    }

    /* Hitung berdasarkan fungsi */
    for (y = y1; y <= y2; y++) {
        int x;
        for (x = x1; x <= x2; x++) {
            if (isi[y][x][0] != '\0') {
                total += atof(isi[y][x]);
                count++;
            }
        }
    }

    if (strcmp(fungsi, "SUM") == 0) {
        *hasil = total;
    } else if (strcmp(fungsi, "AVG") == 0) {
        *hasil = count > 0 ? total / count : 0.0;
    } else if (strcmp(fungsi, "COUNT") == 0) {
        *hasil = count;
    } else if (strcmp(fungsi, "MAX") == 0) {
        double max = 0.0;
        int first = 1;
        for (y = y1; y <= y2; y++) {
            int x;
            for (x = x1; x <= x2; x++) {
                if (isi[y][x][0] != '\0') {
                    double val = atof(isi[y][x]);
                    if (first || val > max) {
                        max = val;
                        first = 0;
                    }
                }
            }
        }
        *hasil = first ? 0.0 : max;
    } else if (strcmp(fungsi, "MIN") == 0) {
        double min = 0.0;
        int first = 1;
        for (y = y1; y <= y2; y++) {
            int x;
            for (x = x1; x <= x2; x++) {
                if (isi[y][x][0] != '\0') {
                    double val = atof(isi[y][x]);
                    if (first || val < min) {
                        min = val;
                        first = 0;
                    }
                }
            }
        }
        *hasil = first ? 0.0 : min;
    } else {
        return -1;
    }

    return 0;
}

static void mode_command_line(struct konfigurasi *cfg)
{
    char buf[MAX_TEXT];
    int len, cursor;
    unsigned char ch;
    char label[64];
    int input_x;

    buf[0] = ':';
    buf[1] = '\0';
    len = 1;
    cursor = 1;
    snprintf(label, sizeof(label), "formula");
    input_x = 2 + (int)strlen(label);

    /* Tampilkan label + isi lama */
    pos(1, 1);
    {
        int i;
        for (i = 0; i < lebar_terminal(); i++) {
            tulis_teks(" ", 1);
        }
    }
    pos(2, 1);
    tulis_teks(label, strlen(label));
    tulis_teks(buf, (size_t)len);
    {
        char judul[] = "TABEL v0.7";
        pos(lebar_terminal() - (int)strlen(judul) - 1, 1);
        tulis_teks(judul, strlen(judul));
    }
    pos(input_x + cursor, 1);
    tulis_teks("\033[?25h", 6);
    flush();

    while (read(STDIN_FILENO, &ch, 1) > 0) {
        if (ch == '\n' || ch == '\r') {
            double hasil;
            if (evaluasi_formula(buf, &hasil) == 0) {
                snprintf(buf, MAX_TEXT, "%.2f", hasil);
                set_cell_text(cfg, cfg->aktif_x, cfg->aktif_y, buf, 1);
                snprintf(status_msg, sizeof(status_msg), "Formula dievaluasi");
            } else {
                snprintf(status_msg, sizeof(status_msg), "Formula tidak valid");
            }
            break;
        } else if (ch == 0x1B) {
            unsigned char s1;
            if (read(STDIN_FILENO, &s1, 1) <= 0) {
                continue;
            }
            if (s1 == '[') {
                unsigned char s2;
                if (read(STDIN_FILENO, &s2, 1) <= 0) {
                    continue;
                }
                if (s2 == 'D') {
                    if (cursor > 1) {
                        cursor--;
                    }
                } else if (s2 == 'C') {
                    if (cursor < len) {
                        cursor++;
                    }
                } else if (s2 == '3') {
                    unsigned char t;
                    if (read(STDIN_FILENO, &t, 1) <= 0) {
                        continue;
                    }
                    if (t == '~') {
                        if (cursor < len) {
                            memmove(buf + cursor, buf + cursor + 1,
                                    (size_t)(len - cursor));
                            len--;
                        }
                    }
                }
            }
        } else if (ch == 0x7F) {
            if (cursor > 1) {
                memmove(buf + cursor - 1, buf + cursor,
                        (size_t)(len - (cursor - 1)));
                cursor--;
                len--;
            }
        } else if (ch >= 0x20 && ch <= 0x7E) {
            if (len < MAX_TEXT - 1) {
                memmove(buf + cursor + 1, buf + cursor,
                        (size_t)(len - cursor));
                buf[cursor] = (char)ch;
                cursor++;
                len++;
                buf[len] = '\0';
            }
        }

        /* Update tampilan */
        pos(1, 1);
        {
            int i;
            for (i = 0; i < lebar_terminal(); i++) {
                tulis_teks(" ", 1);
            }
        }
        pos(2, 1);
        tulis_teks(label, strlen(label));
        tulis_teks(buf, (size_t)len);
        {
            char judul[] = "TABEL v0.7";
            pos(lebar_terminal() - (int)strlen(judul) - 1, 1);
            tulis_teks(judul, strlen(judul));
        }
        pos(input_x + cursor, 1);
        flush();
    }

    tulis_teks("\033[?25l", 6);
    render(cfg);
}

/* ============================================================
 * Fungsi File I/O
 * ============================================================ */
static int simpan_csv(const char *nama_file, struct konfigurasi *cfg)
{
    FILE *file = fopen(nama_file, "w");
    int y, x;
    
    if (!file) {
        snprintf(status_msg, sizeof(status_msg), "Gagal membuka file: %s", nama_file);
        return -1;
    }

    for (y = 0; y < cfg->baris; y++) {
        for (x = 0; x < cfg->kolom; x++) {
            if (x > 0) {
                fprintf(file, ",");
            }
            fprintf(file, "\"%s\"", isi[y][x]);
        }
        fprintf(file, "\n");
    }

    fclose(file);
    snprintf(status_msg, sizeof(status_msg), "File CSV disimpan: %s", nama_file);
    return 0;
}

static int simpan_txt(const char *nama_file, struct konfigurasi *cfg)
{
    FILE *file = fopen(nama_file, "w");
    int y, x;
    
    if (!file) {
        snprintf(status_msg, sizeof(status_msg), "Gagal membuka file: %s", nama_file);
        return -1;
    }

    for (y = 0; y < cfg->baris; y++) {
        for (x = 0; x < cfg->kolom; x++) {
            if (x > 0) {
                fprintf(file, "\t");
            }
            fprintf(file, "%s", isi[y][x]);
        }
        fprintf(file, "\n");
    }

    fclose(file);
    snprintf(status_msg, sizeof(status_msg), "File TXT disimpan: %s", nama_file);
    return 0;
}

static int baca_csv(const char *nama_file, struct konfigurasi *cfg)
{
    FILE *file = fopen(nama_file, "r");
    char baris[MAX_TEXT * MAKS_KOLOM];
    int y = 0;
    int max_x = 0;
    char *token;
    int x;
    
    if (!file) {
        snprintf(status_msg, sizeof(status_msg), "Gagal membuka file: %s", nama_file);
        return -1;
    }

    while (fgets(baris, sizeof(baris), file) && y < cfg->baris) {
        token = strtok(baris, ",\n");
        x = 0;

        while (token && x < cfg->kolom) {
            /* Hapus kutipan jika ada */
            if (token[0] == '"') {
                size_t len = strlen(token);
                if (len > 1 && token[len - 1] == '"') {
                    token[len - 1] = '\0';
                    token++;
                }
            }

            strncpy(isi[y][x], token, MAX_TEXT - 1);
            isi[y][x][MAX_TEXT - 1] = '\0';
            x++;
            token = strtok(NULL, ",\n");
        }

        if (x > max_x) {
            max_x = x;
        }
        y++;
    }

    fclose(file);

    /* Update ukuran grid jika perlu */
    if (max_x > cfg->kolom) {
        cfg->kolom = max_x;
    }
    if (y > cfg->baris) {
        cfg->baris = y;
    }

    snprintf(status_msg, sizeof(status_msg), "File CSV dibaca: %s", nama_file);
    return 0;
}

static int baca_txt(const char *nama_file, struct konfigurasi *cfg)
{
    FILE *file = fopen(nama_file, "r");
    char baris[MAX_TEXT * MAKS_KOLOM];
    int y = 0;
    int max_x = 0;
    char *token;
    int x;
    
    if (!file) {
        snprintf(status_msg, sizeof(status_msg), "Gagal membuka file: %s", nama_file);
        return -1;
    }

    while (fgets(baris, sizeof(baris), file) && y < cfg->baris) {
        token = strtok(baris, "\t\n");
        x = 0;

        while (token && x < cfg->kolom) {
            strncpy(isi[y][x], token, MAX_TEXT - 1);
            isi[y][x][MAX_TEXT - 1] = '\0';
            x++;
            token = strtok(NULL, "\t\n");
        }

        if (x > max_x) {
            max_x = x;
        }
        y++;
    }

    fclose(file);

    /* Update ukuran grid jika perlu */
    if (max_x > cfg->kolom) {
        cfg->kolom = max_x;
    }
    if (y > cfg->baris) {
        cfg->baris = y;
    }

    snprintf(status_msg, sizeof(status_msg), "File TXT dibaca: %s", nama_file);
    return 0;
}

/* ============================================================
 * Fungsi Aksi Modular
 * ============================================================ */

/* Fungsi Undo */
static void aksi_undo(struct konfigurasi *cfg)
{
    if (undo_top <= 0) {
        snprintf(status_msg, sizeof(status_msg), "Tidak ada yang bisa di-undo");
        return;
    }

    undo_top--;
    {
        struct op op = undo_stack[undo_top];
        if (redo_top >= UNDO_MAX) {
            redo_top = UNDO_MAX - 1;
        }
        redo_stack[redo_top].x = op.x;
        redo_stack[redo_top].y = op.y;
        strncpy(redo_stack[redo_top].before, isi[op.y][op.x], MAX_TEXT - 1);
        redo_stack[redo_top].before[MAX_TEXT - 1] = '\0';
        strncpy(redo_stack[redo_top].after, op.after, MAX_TEXT - 1);
        redo_stack[redo_top].after[MAX_TEXT - 1] = '\0';
        redo_top++;
        strncpy(isi[op.y][op.x], op.before, MAX_TEXT - 1);
        isi[op.y][op.x][MAX_TEXT - 1] = '\0';
    }
    snprintf(status_msg, sizeof(status_msg), "Undo berhasil");
}

/* Fungsi Redo */
static void aksi_redo(struct konfigurasi *cfg)
{
    if (redo_top <= 0) {
        snprintf(status_msg, sizeof(status_msg), "Tidak ada yang bisa di-redo");
        return;
    }

    redo_top--;
    {
        struct op op = redo_stack[redo_top];
        push_undo(op.x, op.y, isi[op.y][op.x], op.after);
        strncpy(isi[op.y][op.x], op.after, MAX_TEXT - 1);
        isi[op.y][op.x][MAX_TEXT - 1] = '\0';
    }
    snprintf(status_msg, sizeof(status_msg), "Redo berhasil");
}

/* Fungsi Seleksi */
static void update_seleksi_status(const struct konfigurasi *cfg)
{
    if (!selecting) return;

    int minx = sel_anchor_x < cfg->aktif_x ? sel_anchor_x : cfg->aktif_x;
    int maxx = sel_anchor_x > cfg->aktif_x ? sel_anchor_x : cfg->aktif_x;
    int miny = sel_anchor_y < cfg->aktif_y ? sel_anchor_y : cfg->aktif_y;
    int maxy = sel_anchor_y > cfg->aktif_y ? sel_anchor_y : cfg->aktif_y;

    /* Hitung jumlah sel yang terseleksi */
    int count = (maxx - minx + 1) * (maxy - miny + 1);

    /* Update status message */
    snprintf(status_msg, sizeof(status_msg), "Memilih kolom %c%d - %c%d (%d Sel)",
             'A' + minx, miny + 1, 'A' + maxx, maxy + 1, count);
}

static void aksi_seleksi(struct konfigurasi *cfg)
{
    selecting = 1;
    sel_anchor_x = cfg->aktif_x;
    sel_anchor_y = cfg->aktif_y;
    prev_sel_x = cfg->aktif_x;
    prev_sel_y = cfg->aktif_y;
    snprintf(status_msg, sizeof(status_msg), "Memilih kolom %c%d",
             'A' + cfg->aktif_x, cfg->aktif_y + 1);
    redraw_seleksi_parsial(cfg);
}

static void akhiri_seleksi(struct konfigurasi *cfg)
{
    if (!selecting) return;

    selecting = 0;

    /* Simpan area yang terseleksi ke clipboard */
    int minx = sel_anchor_x < cfg->aktif_x ? sel_anchor_x : cfg->aktif_x;
    int maxx = sel_anchor_x > cfg->aktif_x ? sel_anchor_x : cfg->aktif_x;
    int miny = sel_anchor_y < cfg->aktif_y ? sel_anchor_y : cfg->aktif_y;
    int maxy = sel_anchor_y > cfg->aktif_y ? sel_anchor_y : cfg->aktif_y;

    clip_x1 = minx;
    clip_y1 = miny;
    clip_x2 = maxx;
    clip_y2 = maxy;
    clip_has_area = 1;

    /* Salin isi sel ke clipboard_area */
    int r, c;
    for (r = miny; r <= maxy; r++) {
        for (c = minx; c <= maxx; c++) {
            strncpy(clipboard_area[r][c], isi[r][c], MAX_TEXT - 1);
            clipboard_area[r][c][MAX_TEXT - 1] = '\0';
        }
    }

    render(cfg);
}

/* Fungsi Copy */
static void aksi_copy(struct konfigurasi *cfg)
{
    int x1, y1, x2, y2, xx, yy;
    int minx, maxx, miny, maxy;

    if (selecting) {
        x1 = sel_anchor_x;
        y1 = sel_anchor_y;
        x2 = cfg->aktif_x;
        y2 = cfg->aktif_y;

        if (x1 > x2) {
            int t = x1;
            x1 = x2;
            x2 = t;
        }
        if (y1 > y2) {
            int t = y1;
            y1 = y2;
            y2 = t;
        }

        clip_x1 = x1;
        clip_y1 = y1;
        clip_x2 = x2;
        clip_y2 = y2;
        clip_has_area = 1;

        for (yy = y1; yy <= y2; yy++) {
            for (xx = x1; xx <= x2; xx++) {
                strncpy(clipboard_area[yy][xx], isi[yy][xx], MAX_TEXT - 1);
                clipboard_area[yy][xx][MAX_TEXT - 1] = '\0';
            }
        }

        selecting = 0;
        sel_anchor_x = sel_anchor_y = -1;
        prev_sel_x = -1;
        prev_sel_y = -1;
        snprintf(status_msg, sizeof(status_msg), "Area disalin");
    } else {
        /* Single cell copy */
        strncpy(clipboard, isi[cfg->aktif_y][cfg->aktif_x], MAX_TEXT - 1);
        clipboard[MAX_TEXT - 1] = '\0';
        clip_x1 = clip_x2 = cfg->aktif_x;
        clip_y1 = clip_y2 = cfg->aktif_y;
        strncpy(clipboard_area[clip_y1][clip_x1], clipboard, MAX_TEXT - 1);
        clipboard_area[clip_y1][clip_x1][MAX_TEXT - 1] = '\0';
        clip_has_area = 1;
        snprintf(status_msg, sizeof(status_msg), "Sel %c%d disalin",
                 'A' + cfg->aktif_x, cfg->aktif_y + 1);
    }
}

/* Fungsi Cut */
static void aksi_cut(struct konfigurasi *cfg)
{
    int x1, y1, x2, y2, xx, yy;
    int minx, maxx, miny, maxy;

    if (selecting) {
        x1 = sel_anchor_x;
        y1 = sel_anchor_y;
        x2 = cfg->aktif_x;
        y2 = cfg->aktif_y;

        if (x1 > x2) {
            int t = x1;
            x1 = x2;
            x2 = t;
        }
        if (y1 > y2) {
            int t = y1;
            y1 = y2;
            y2 = t;
        }

        clip_x1 = x1;
        clip_y1 = y1;
        clip_x2 = x2;
        clip_y2 = y2;
        clip_has_area = 1;

        for (yy = y1; yy <= y2; yy++) {
            for (xx = x1; xx <= x2; xx++) {
                strncpy(clipboard_area[yy][xx], isi[yy][xx], MAX_TEXT - 1);
                clipboard_area[yy][xx][MAX_TEXT - 1] = '\0';
                set_cell_text(cfg, xx, yy, "", 1);
            }
        }

        selecting = 0;
        sel_anchor_x = sel_anchor_y = -1;
        prev_sel_x = -1;
        prev_sel_y = -1;
        snprintf(status_msg, sizeof(status_msg), "Area dipotong");
    } else {
        /* Single cell cut */
        strncpy(clipboard, isi[cfg->aktif_y][cfg->aktif_x], MAX_TEXT - 1);
        clipboard[MAX_TEXT - 1] = '\0';
        clip_x1 = clip_x2 = cfg->aktif_x;
        clip_y1 = clip_y2 = cfg->aktif_y;
        strncpy(clipboard_area[clip_y1][clip_x1], clipboard, MAX_TEXT - 1);
        clipboard_area[clip_y1][clip_x1][MAX_TEXT - 1] = '\0';
        clip_has_area = 1;
        set_cell_text(cfg, cfg->aktif_x, cfg->aktif_y, "", 1);
        snprintf(status_msg, sizeof(status_msg), "Sel %c%d dipotong",
                 'A' + cfg->aktif_x, cfg->aktif_y + 1);
    }
}

/* Fungsi Paste */
static void aksi_paste(struct konfigurasi *cfg)
{
    int src_w, src_h, dx, dy;

    if (clip_has_area) {
        src_w = clip_x2 - clip_x1 + 1;
        src_h = clip_y2 - clip_y1 + 1;
        for (dy = 0; dy < src_h; dy++) {
            for (dx = 0; dx < src_w; dx++) {
                int tx = cfg->aktif_x + dx;
                int ty = cfg->aktif_y + dy;
                int sx = clip_x1 + dx;
                int sy = clip_y1 + dy;
                if (tx >= 0 && tx < cfg->kolom && ty >= 0 && ty < cfg->baris) {
                    set_cell_text(cfg, tx, ty, clipboard_area[sy][sx], 1);
                }
            }
        }
        /* Hapus penanda hijau setelah paste */
        clip_has_area = 0;
        snprintf(status_msg, sizeof(status_msg), "Area ditempel");
    } else {
        set_cell_text(cfg, cfg->aktif_x, cfg->aktif_y, clipboard, 1);
        snprintf(status_msg, sizeof(status_msg), "Sel ditempel");
    }
}

/* Fungsi Resize Kolom */
static void aksi_resize_kolom(struct konfigurasi *cfg, int arah)
{
    if (arah > 0) {
        if (lebar_kolom[cfg->aktif_x] < 30) {
            lebar_kolom[cfg->aktif_x]++;
            snprintf(status_msg, sizeof(status_msg), "Lebar kolom %c: %d",
                     'A' + cfg->aktif_x, lebar_kolom[cfg->aktif_x]);
        } else {
            snprintf(status_msg, sizeof(status_msg), "Lebar kolom maksimal");
        }
    } else {
        if (lebar_kolom[cfg->aktif_x] > 3) {
            lebar_kolom[cfg->aktif_x]--;
            snprintf(status_msg, sizeof(status_msg), "Lebar kolom %c: %d",
                     'A' + cfg->aktif_x, lebar_kolom[cfg->aktif_x]);
        } else {
            snprintf(status_msg, sizeof(status_msg), "Lebar kolom minimal");
        }
    }
}

/* Fungsi Resize Baris */
static void aksi_resize_baris(struct konfigurasi *cfg, int arah)
{
    if (arah > 0) {
        if (tinggi_baris[cfg->aktif_y] < 10) {
            tinggi_baris[cfg->aktif_y]++;
            snprintf(status_msg, sizeof(status_msg), "Tinggi baris %d: %d",
                     cfg->aktif_y + 1, tinggi_baris[cfg->aktif_y]);
        } else {
            snprintf(status_msg, sizeof(status_msg), "Tinggi baris maksimal");
        }
    } else {
        if (tinggi_baris[cfg->aktif_y] > 1) {
            tinggi_baris[cfg->aktif_y]--;
            snprintf(status_msg, sizeof(status_msg), "Tinggi baris %d: %d",
                     cfg->aktif_y + 1, tinggi_baris[cfg->aktif_y]);
        } else {
            snprintf(status_msg, sizeof(status_msg), "Tinggi baris minimal");
        }
    }
}

/* Fungsi Goto Cell */
static void aksi_goto_cell(struct konfigurasi *cfg)
{
    char buf[16];
    int i = 0;
    unsigned char ch;
    int x = -1, y = -1;

    pos(2, tinggi_terminal());
    tulis_teks("Goto: ", 6);
    flush();

    while (i < 15 && read(STDIN_FILENO, &ch, 1) > 0) {
        if (ch == '\n' || ch == '\r') {
            break;
        }
        if (ch >= 'a' && ch <= 'z') {
            ch = ch - 'a' + 'A';
        }
        if ((ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9')) {
            buf[i++] = ch;
            tulis_teks(&ch, 1);
            flush();
        }
    }
    buf[i] = '\0';

    if (i > 0) {
        if (buf[0] >= 'A' && buf[0] <= 'Z') {
            x = buf[0] - 'A';
            if (i > 1) {
                y = atoi(buf + 1) - 1;
            }
        }

        if (x >= 0 && x < cfg->kolom && y >= 0 && y < cfg->baris) {
            cfg->prev_x = cfg->aktif_x;
            cfg->prev_y = cfg->aktif_y;
            cfg->aktif_x = x;
            cfg->aktif_y = y;
            ensure_active_visible(cfg);
            snprintf(status_msg, sizeof(status_msg), "Pindah ke sel %c%d",
                     'A' + x, y + 1);
        } else {
            snprintf(status_msg, sizeof(status_msg), "Sel tidak valid: %s", buf);
        }
    }
}

/* Fungsi Simpan File */
static void aksi_simpan_file(struct konfigurasi *cfg)
{
    char nama_file[MAX_NAMA_FILE];
    int i = 0;
    unsigned char ch;
    int format_csv = 0; /* 0 = txt, 1 = csv */

    pos(2, tinggi_terminal());
    tulis_teks("Simpan (format: .txt atau .csv): ", 32);
    flush();

    while (i < MAX_NAMA_FILE - 1 && read(STDIN_FILENO, &ch, 1) > 0) {
        if (ch == '\n' || ch == '\r') {
            break;
        }
        if (ch >= 0x20 && ch <= 0x7E) {
            nama_file[i++] = ch;
            tulis_teks(&ch, 1);
            flush();
        }
    }
    nama_file[i] = '\0';

    /* Periksa ekstensi file */
    if (i > 4 && nama_file[i - 4] == '.' && 
        (nama_file[i - 3] == 'c' || nama_file[i - 3] == 'C') &&
        (nama_file[i - 2] == 's' || nama_file[i - 2] == 'S') &&
        (nama_file[i - 1] == 'v' || nama_file[i - 1] == 'V')) {
        format_csv = 1;
    }

    if (i > 0) {
        if (format_csv) {
            simpan_csv(nama_file, cfg);
        } else {
            simpan_txt(nama_file, cfg);
        }
    }
}

/* Fungsi Buka File */
static void aksi_buka_file(struct konfigurasi *cfg)
{
    char nama_file[MAX_NAMA_FILE];
    int i = 0;
    unsigned char ch;
    int format_csv = 0; /* 0 = txt, 1 = csv */

    pos(2, tinggi_terminal());
    tulis_teks("Buka (format: .txt atau .csv): ", 30);
    flush();

    while (i < MAX_NAMA_FILE - 1 && read(STDIN_FILENO, &ch, 1) > 0) {
        if (ch == '\n' || ch == '\r') {
            break;
        }
        if (ch >= 0x20 && ch <= 0x7E) {
            nama_file[i++] = ch;
            tulis_teks(&ch, 1);
            flush();
        }
    }
    nama_file[i] = '\0';

    /* Periksa ekstensi file */
    if (i > 4 && nama_file[i - 4] == '.' && 
        (nama_file[i - 3] == 'c' || nama_file[i - 3] == 'C') &&
        (nama_file[i - 2] == 's' || nama_file[i - 2] == 'S') &&
        (nama_file[i - 1] == 'v' || nama_file[i - 1] == 'V')) {
        format_csv = 1;
    }

    if (i > 0) {
        if (format_csv) {
            baca_csv(nama_file, cfg);
        } else {
            baca_txt(nama_file, cfg);
        }
    }
}

/* Fungsi Bantuan */
static void aksi_bantuan(void)
{
    int rows = tinggi_terminal();
    const char *help[] = {
        "=== Bantuan TABEL v0.7 ===",
        "",
        "Navigasi:",
        "  Panah ←↑→↓  : pindah sel",
        "",
        "Edit:",
        "  Enter       : edit sel",
        "  Tab         : commit & pindah ke sel berikutnya (dalam mode edit)",
        "  :           : command line untuk formula",
        "",
        "File:",
        "  w           : simpan file",
        "  e           : buka file",
        "",
        "Seleksi & Clipboard:",
        "  v           : mulai/batal seleksi area",
        "  y / x / p   : copy / cut / paste",
        "",
        "Resize:",
        "  Alt+←→      : ubah lebar kolom",
        "  Alt+↑↓      : ubah tinggi baris",
        "",
        "Lainnya:",
        "  u / U       : undo / redo",
        "  g{col}{row} : lompat ke sel (ga25 → A25)",
        "  q           : keluar",
    };
    int n = (int)(sizeof(help) / sizeof(help[0])), i;
    unsigned char ch;
    
    bersih();
    for (i = 0; i < n && i < rows - 2; i++) {
        pos(2, 2 + i);
        tulis_teks(help[i], strlen(help[i]));
    }
    pos(2, rows - 1);
    tulis_teks("Tekan tombol apapun untuk kembali...", 36);
    flush();
    read(STDIN_FILENO, &ch, 1);
}

/* ============================================================
 * Fungsi Inisialisasi
 * ============================================================ */
static int inisialisasi_data(struct konfigurasi *cfg, int argc, char **argv)
{
    int i, xx, yy;
    int k, b;

    cfg->kolom = 10;
    cfg->baris = 10;
    cfg->aktif_x = 0;
    cfg->aktif_y = 0;
    cfg->view_col = 0;
    cfg->view_row = 0;
    cfg->prev_x = 0;
    cfg->prev_y = 0;

    if (argc >= 3) {
        k = atoi(argv[1]);
        b = atoi(argv[2]);
        if (k <= 0 || b <= 0) {
            return -1;
        }
        if (k > MAKS_KOLOM) {
            k = MAKS_KOLOM;
        }
        if (b > MAKS_BARIS) {
            b = MAKS_BARIS;
        }
        cfg->kolom = k;
        cfg->baris = b;
    }

    for (i = 0; i < cfg->kolom; i++) {
        lebar_kolom[i] = 8;
    }
    for (i = 0; i < cfg->baris; i++) {
        tinggi_baris[i] = 1;
    }
    for (yy = 0; yy < cfg->baris; yy++) {
        for (xx = 0; xx < cfg->kolom; xx++) {
            isi[yy][xx][0] = '\0';
            align_sel[yy][xx] = LEFT;
        }
    }

    clipboard[0] = '\0';
    undo_top = 0;
    redo_top = 0;
    selecting = 0;
    sel_anchor_x = sel_anchor_y = -1;
    prev_sel_x = prev_sel_y = -1;
    clip_has_area = 0;
    clip_x1 = clip_y1 = clip_x2 = clip_y2 = -1;

    return 0;
}

/* ============================================================
 * Fungsi Loop Utama
 * ============================================================ */
static int loop(struct konfigurasi *cfg)
{
    unsigned char ch;
    int viewport_changed = 0;
    int old_view_col, old_view_row;

    while (1) {
        if (read(STDIN_FILENO, &ch, 1) <= 0) {
            return -1;
        }

        if (ch == 'q' || ch == 'Q') {
            return 0;
        }

        /* Navigasi */
        if (ch == 0x1B) {
            unsigned char seq0, seq1;
            if (read(STDIN_FILENO, &seq0, 1) <= 0) {
                continue;
            }
            if (seq0 == '[') {
                if (read(STDIN_FILENO, &seq1, 1) <= 0) {
                    continue;
                }

                old_view_col = cfg->view_col;
                old_view_row = cfg->view_row;

                if (seq1 == 'A') {
                    move_up(cfg);
                } else if (seq1 == 'B') {
                    move_down(cfg);
                } else if (seq1 == 'C') {
                    move_right(cfg);
                } else if (seq1 == 'D') {
                    move_left(cfg);
                }

                /* Periksa apakah viewport perlu diubah */
                ensure_active_visible(cfg);
                viewport_changed = (old_view_col != cfg->view_col || 
                                  old_view_row != cfg->view_row);

                if (viewport_changed) {
                    render(cfg);
                } else {
                    redraw_navigasi_parsial(cfg);
                }
                continue;
            }
            /* Alt+arrow: ESC [ 1 ; 3 A/B/C/D */
            else if (seq0 == '1') {
                unsigned char semi, three, dir;
                if (read(STDIN_FILENO, &semi, 1) <= 0) {
                    continue;
                }
                if (read(STDIN_FILENO, &three, 1) <= 0) {
                    continue;
                }
                if (read(STDIN_FILENO, &dir, 1) <= 0) {
                    continue;
                }
                if (semi == ';' && three == '3') {
                    if (dir == 'A') {
                        aksi_resize_baris(cfg, -1);
                    } else if (dir == 'B') {
                        aksi_resize_baris(cfg, 1);
                    } else if (dir == 'C') {
                        aksi_resize_kolom(cfg, 1);
                    } else if (dir == 'D') {
                        aksi_resize_kolom(cfg, -1);
                    }
                    render(cfg);
                    continue;
                }
            }
        }

        /* Edit */
        if (ch == '\n') {
            mode_edit(cfg);
            continue;
        }

        /* Command line */
        if (ch == ':') {
            mode_command_line(cfg);
            continue;
        }

        /* Aksi modular */
        if (ch == 'u') {
            aksi_undo(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'U') {
            aksi_redo(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'v') {
            aksi_seleksi(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'y') {
            aksi_copy(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'x') {
            aksi_cut(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'p') {
            aksi_paste(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'g') {
            aksi_goto_cell(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'w') {
            aksi_simpan_file(cfg);
            render(cfg);
            continue;
        }
        if (ch == 'e') {
            aksi_buka_file(cfg);
            render(cfg);
            continue;
        }
        if (ch == '?') {
            aksi_bantuan();
            render(cfg);
            continue;
        }
    }
}

/* ============================================================
 * Fungsi Utama
 * ============================================================ */
int main(int argc, char *argv[])
{
    struct konfigurasi cfg;
    int st;

    signal(SIGINT, tangani_sinyal);
    signal(SIGTERM, tangani_sinyal);

    if (inisialisasi_terminal() != 0) {
        fprintf(stderr, "Gagal inisialisasi terminal\n");
        return 1;
    }

    if (inisialisasi_buffer(&back_buffer, 4096) != 0) {
        fprintf(stderr, "Gagal inisialisasi buffer\n");
        pulihkan_terminal();
        return 1;
    }

    if (inisialisasi_data(&cfg, argc, argv) != 0) {
        fprintf(stderr, "Penggunaan: %s [KOL] [BAR]\n", argv[0]);
        bersihkan_buffer(&back_buffer);
        pulihkan_terminal();
        return 1;
    }

    masuk_alt();
    bersih();
    render(&cfg);

    st = loop(&cfg);

    bersihkan_buffer(&back_buffer);
    pulihkan_terminal();
    keluar_alt();
    tulis_teks(ESC_CLR ESC_HOME, 7);
    flush();

    return st == 0 ? 0 : 1;
}
