/* See LICENSE file for copyright and license details. */

/* appearance */
static const char font[]            = "-*-*-medium-*-*-*-14-*-*-*-*-*-*-*";
static const uint16_t normbordercolor[] = { 0xcc00, 0xcc00, 0xcc00 };
static const uint16_t normbgcolor[]     = { 0xcc00, 0xcc00, 0xcc00 };
static const uint16_t normfgcolor[]     = { 0, 0, 0 };
static const uint16_t selbordercolor[]  = { 0, 0x6600, 0xffff };
static const uint16_t selbgcolor[]      = { 0, 0x6600, 0xffff };
static const uint16_t selfgcolor[]      = { 0xffff, 0xffff, 0xffff };
static const unsigned int borderpx  = 1;        /* border pixel of windows */
static const unsigned int snap      = 32;       /* snap pixel */
static const int showbar           = true;     /* false means no bar */
static const int topbar            = true;     /* false means bottom bar */

/* tagging */
static const char *tags[] = { "1", "2", "3", "4", "5", "6", "7", "8", "9" };

static const Rule rules[] = {
	/* class      instance    title       tags mask     isfloating   monitor */
	{ "Gimp",     NULL,       NULL,       0,            true,        -1 },
    // ImageMagick
	{ "display",  NULL,       NULL,       0,            true,        -1 },
	// Various browsers
	{ "Firefox",  NULL,       NULL,       1 << 8,       false,       -1 },
	{ "Namoroka", NULL,       NULL,       1 << 8,       false,       -1 },
	{ "Midori",   NULL,       NULL,       1 << 8,       false,       -1 },
	{ "Epiphany", NULL,       NULL,       1 << 8,       false,       -1 },
};

/* layout(s) */
static const float mfact      = 0.55f; /* factor of master area size [0.05..0.95] */
static const int resizehints = true; /* true means respect size hints in tiled resizals */

static const Layout layouts[] = {
	/* symbol     arrange function */
	{ "[]=",      tile },    /* first entry is default */
	{ "><>",      NULL },    /* no layout function means floating behavior */
	{ "[M]",      monocle },
};

/* key definitions */
#define MODKEY XCB_MOD_MASK_1
#define TAGKEYS(KEY,TAG) \
	{ MODKEY,                       KEY,      view,           {.ui = 1 << TAG} }, \
	{ MODKEY|XCB_MOD_MASK_CONTROL,  KEY,      toggleview,     {.ui = 1 << TAG} }, \
	{ MODKEY|XCB_MOD_MASK_SHIFT,    KEY,      tag,            {.ui = 1 << TAG} }, \
	{ MODKEY|XCB_MOD_MASK_CONTROL|XCB_MOD_MASK_SHIFT, \
                                        KEY,      toggletag,      {.ui = 1 << TAG} },

/* helper for spawning shell commands in the pre dwm-5.0 fashion */
#define SHCMD(cmd) { .v = (const char*[]){ "/bin/sh", "-c", cmd, NULL } }

/* commands */
// static const char *dmenucmd[] = { "dmenu_run", "-fn", font, "-nb", normbgcolor, "-nf", normfgcolor, "-sb", selbgcolor, "-sf", selfgcolor, NULL };
static const char *termcmd[]  = { "uxterm", NULL };

static Key keys[] = {
	/* modifier                     key        function        argument */
	{ MODKEY,                       XK_p,      spawn,          {.v = dmenucmd } },
	{ MODKEY|XCB_MOD_MASK_SHIFT,    XK_Return, spawn,          {.v = termcmd } },
	{ MODKEY,                       XK_b,      togglebar,      {0} },
	{ MODKEY,                       XK_j,      focusstack,     {.i = +1 } },
	{ MODKEY,                       XK_k,      focusstack,     {.i = -1 } },
	{ XCB_MOD_MASK_1,               XK_Tab,    focusstack,     {.i = +1 } },
	{ XCB_MOD_MASK_1|XCB_MOD_MASK_SHIFT, XK_Tab, focusstack,   {.i = -1 } },
	{ MODKEY,                       XK_h,      setmfact,       {.f = -0.05f} },
	{ MODKEY,                       XK_l,      setmfact,       {.f = +0.05f} },
	{ MODKEY,                       XK_Return, zoom,           {0} },
	{ MODKEY,                       XK_Tab,    view,           {0} },
	{ MODKEY|XCB_MOD_MASK_SHIFT,    XK_c,      killclient,     {0} },
	{ MODKEY,                       XK_t,      setlayout,      {.v = &layouts[0]} },
	{ MODKEY,                       XK_f,      setlayout,      {.v = &layouts[1]} },
	{ MODKEY,                       XK_m,      setlayout,      {.v = &layouts[2]} },
	{ MODKEY,                       XK_space,  setlayout,      {0} },
	{ MODKEY|XCB_MOD_MASK_SHIFT,    XK_space,  togglefloating, {0} },
	{ MODKEY,                       XK_0,      view,           {.ui = ~0 } },
	{ MODKEY|XCB_MOD_MASK_SHIFT,    XK_0,      tag,            {.ui = ~0 } },
	{ MODKEY,                       XK_comma,  focusmon,       {.i = -1 } },
	{ MODKEY,                       XK_period, focusmon,       {.i = +1 } },
	{ MODKEY|XCB_MOD_MASK_SHIFT,    XK_comma,  tagmon,         {.i = -1 } },
	{ MODKEY|XCB_MOD_MASK_SHIFT,    XK_period, tagmon,         {.i = +1 } },
	TAGKEYS(                        XK_1,                      0)
	TAGKEYS(                        XK_2,                      1)
	TAGKEYS(                        XK_3,                      2)
	TAGKEYS(                        XK_4,                      3)
	TAGKEYS(                        XK_5,                      4)
	TAGKEYS(                        XK_6,                      5)
	TAGKEYS(                        XK_7,                      6)
	TAGKEYS(                        XK_8,                      7)
	TAGKEYS(                        XK_9,                      8)
	{ MODKEY,                       XK_Left,   viewprev,        {0} },
	{ MODKEY,                       XK_Right,  viewnext,        {0} },
	{ MODKEY|XCB_MOD_MASK_SHIFT,             XK_q,      quit,           {0} },
};

/* button definitions */
/* click can be ClkLtSymbol, ClkStatusText, ClkWinTitle, ClkClientWin, or ClkRootWin */
static Button buttons[] = {
	/* click                event mask      button          function        argument */
	{ ClkLtSymbol,          0,              1,        setlayout,      {0} },
	{ ClkLtSymbol,          0,              3,        setlayout,      {.v = &layouts[2]} },
	{ ClkWinTitle,          0,              2,        zoom,           {0} },
	{ ClkStatusText,        0,              2,        spawn,          {.v = termcmd } },
	{ ClkClientWin,         MODKEY,         1,        movemouse,      {0} },
	{ ClkClientWin,         MODKEY,         2,        togglefloating, {0} },
	{ ClkClientWin,         MODKEY,         3,        resizemouse,    {0} },
	{ ClkTagBar,            0,              1,        view,           {0} },
	{ ClkTagBar,            0,              3,        toggleview,     {0} },
	{ ClkTagBar,            MODKEY,         1,        tag,            {0} },
	{ ClkTagBar,            MODKEY,         3,        toggletag,      {0} },
};

