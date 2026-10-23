// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.lexer;
import astopt;

import std.array;
import std.string, utf = std.utf, std.uni;
import std.conv;
import std.algorithm;
import std.traits: EnumMembers;
import util.tuple;
import std.utf;

//import core.memory;

import util : lowerf, escape, toEngNum, displayWidth;

mixin("enum TokenType{"~TokenNames()~"}");

template Tok(string type){mixin(TokImpl());}
template TokChars(TokenType type){mixin(TokCharsImpl());}

bool isAlphaEx(dchar c){
	import std.algorithm : canFind;
	return isAlpha(c)||canFind("𝟘𝟙∏₀₁₂₃₄₅₆₇₈₉₋₊⁰¹²³⁴⁵⁶⁷⁸⁹⁻⁺"d,c);
}

// Unicode hardening (avoids "Trojan Source", CVE-2021-42574)
/// Unicode Bidi_Control characters.
bool isBidiControl(dchar c){
	return c==0x061C||c==0x200E||c==0x200F||(0x202A<=c&&c<=0x202E)||(0x2066<=c&&c<=0x2069);
}
/// Unicode Default_Ignorable_Code_Point (DerivedCoreProperties.txt, Unicode 15.1).
bool isDefaultIgnorable(dchar c){
	if(c<0x80) return false;
	return c==0x00AD||c==0x034F||c==0x061C||c==0x115F||c==0x1160||c==0x17B4||c==0x17B5
		||(0x180B<=c&&c<=0x180F)||(0x200B<=c&&c<=0x200F)||(0x202A<=c&&c<=0x202E)
		||(0x2060<=c&&c<=0x206F)||c==0x3164||(0xFE00<=c&&c<=0xFE0F)||c==0xFEFF||c==0xFFA0
		||(0xFFF0<=c&&c<=0xFFF8)||(0x1BCA0<=c&&c<=0x1BCA3)||(0x1D173<=c&&c<=0x1D17A)
		||(0xE0000<=c&&c<=0xE0FFF);
}
/// non-ASCII line breaks (treated as line breaks by some editors, but not by this lexer).
bool isUnicodeLineBreak(dchar c){ return c==0x85||c==0x2028||c==0x2029; }
/// C1 control characters.
bool isC1Control(dchar c){ return 0x80<=c&&c<=0x9F; }
/// letters (according to std.uni.isAlpha) that are invisible or look like ASCII punctuation.
bool isMisleadingLetter(dchar c){
	return (0x01C0<=c&&c<=0x01C3) // click letters: ǀ ǁ ǂ ǃ
		||(0x02B9<=c&&c<=0x02BD)||c==0x02C6||(0x02C8<=c&&c<=0x02CD)||c==0x02D0||c==0x02D1||c==0x02EE // modifier letters: ʹ ʺ ʻ ʼ ʽ ˆ ˈ ˉ ˊ ˋ ˌ ˍ ː ˑ ˮ
		||(0xA4F8<=c&&c<=0xA4FD) // Lisu tone letters: ꓸ ꓹ ꓺ ꓻ ꓼ ꓽ
		||c==0xA78F||c==0x1427||c==0x2D51 // ꞏ ᐧ ⵑ
		||c==0x115F||c==0x1160||c==0x3164||c==0xFFA0; // Hangul fillers (invisible)
}
/// characters that are rejected anywhere in a source file, including comments and string literals.
bool isForbiddenInText(dchar c){
	return isBidiControl(c)||isUnicodeLineBreak(c)||isC1Control(c);
}
/// whether `c` may appear in an identifier.
bool isIdentChar(dchar c){ return isAlphaEx(c)&&!identifierCharProblem(c); }
/// returns null if `c` may appear in an identifier, otherwise the reason why not. (Precondition: isAlphaEx(c).)
string identifierCharProblem(dchar c){
	if(isDefaultIgnorable(c)) return "it is invisible";
	if(isMisleadingLetter(c)) return "it is invisible or looks like ASCII punctuation";
	if(!allowedIn!NFC(c)){ // (e.g. U+2126 OHM SIGN, U+212A KELVIN SIGN, Greek letters with oxia, which look like their NFC equivalents)
		auto nfc=normalize!NFC(to!string(c));
		if(nfc.length&&nfc!=to!string(c)) return format("it is not in Unicode normalization form C; use %s instead",describeChars(nfc));
		return "it may not be in Unicode normalization form C";
	}
	return null;
}
/// Unicode names of the characters this lexer rejects, for diagnostics.
string charName(dchar c){
	if(0xFE00<=c&&c<=0xFE0F) return "VARIATION SELECTOR";
	if(0xE0100<=c&&c<=0xE01EF) return "VARIATION SELECTOR";
	if(0xE0000<=c&&c<=0xE007F) return "TAG CHARACTER";
	switch(c){
		case 0x00A0: return "NO-BREAK SPACE";
		case 0x1680: return "OGHAM SPACE MARK";
		case 0x2000: return "EN QUAD";
		case 0x2001: return "EM QUAD";
		case 0x2002: return "EN SPACE";
		case 0x2003: return "EM SPACE";
		case 0x2004: return "THREE-PER-EM SPACE";
		case 0x2005: return "FOUR-PER-EM SPACE";
		case 0x2006: return "SIX-PER-EM SPACE";
		case 0x2007: return "FIGURE SPACE";
		case 0x2008: return "PUNCTUATION SPACE";
		case 0x2009: return "THIN SPACE";
		case 0x200A: return "HAIR SPACE";
		case 0x202F: return "NARROW NO-BREAK SPACE";
		case 0x205F: return "MEDIUM MATHEMATICAL SPACE";
		case 0x3000: return "IDEOGRAPHIC SPACE";
		case 0x0085: return "NEXT LINE";
		case 0x2028: return "LINE SEPARATOR";
		case 0x2029: return "PARAGRAPH SEPARATOR";
		case 0x00AD: return "SOFT HYPHEN";
		case 0x034F: return "COMBINING GRAPHEME JOINER";
		case 0x061C: return "ARABIC LETTER MARK";
		case 0x115F: return "HANGUL CHOSEONG FILLER";
		case 0x1160: return "HANGUL JUNGSEONG FILLER";
		case 0x17B4: return "KHMER VOWEL INHERENT AQ";
		case 0x17B5: return "KHMER VOWEL INHERENT AA";
		case 0x180B: return "MONGOLIAN FREE VARIATION SELECTOR ONE";
		case 0x180C: return "MONGOLIAN FREE VARIATION SELECTOR TWO";
		case 0x180D: return "MONGOLIAN FREE VARIATION SELECTOR THREE";
		case 0x180E: return "MONGOLIAN VOWEL SEPARATOR";
		case 0x180F: return "MONGOLIAN FREE VARIATION SELECTOR FOUR";
		case 0x200B: return "ZERO WIDTH SPACE";
		case 0x200C: return "ZERO WIDTH NON-JOINER";
		case 0x200D: return "ZERO WIDTH JOINER";
		case 0x200E: return "LEFT-TO-RIGHT MARK";
		case 0x200F: return "RIGHT-TO-LEFT MARK";
		case 0x202A: return "LEFT-TO-RIGHT EMBEDDING";
		case 0x202B: return "RIGHT-TO-LEFT EMBEDDING";
		case 0x202C: return "POP DIRECTIONAL FORMATTING";
		case 0x202D: return "LEFT-TO-RIGHT OVERRIDE";
		case 0x202E: return "RIGHT-TO-LEFT OVERRIDE";
		case 0x2060: return "WORD JOINER";
		case 0x2061: return "FUNCTION APPLICATION";
		case 0x2062: return "INVISIBLE TIMES";
		case 0x2063: return "INVISIBLE SEPARATOR";
		case 0x2064: return "INVISIBLE PLUS";
		case 0x2066: return "LEFT-TO-RIGHT ISOLATE";
		case 0x2067: return "RIGHT-TO-LEFT ISOLATE";
		case 0x2068: return "FIRST STRONG ISOLATE";
		case 0x2069: return "POP DIRECTIONAL ISOLATE";
		case 0x206A: return "INHIBIT SYMMETRIC SWAPPING";
		case 0x206B: return "ACTIVATE SYMMETRIC SWAPPING";
		case 0x206C: return "INHIBIT ARABIC FORM SHAPING";
		case 0x206D: return "ACTIVATE ARABIC FORM SHAPING";
		case 0x206E: return "NATIONAL DIGIT SHAPES";
		case 0x206F: return "NOMINAL DIGIT SHAPES";
		case 0x3164: return "HANGUL FILLER";
		case 0xFEFF: return "ZERO WIDTH NO-BREAK SPACE (byte order mark)";
		case 0xFFA0: return "HALFWIDTH HANGUL FILLER";
		case 0x1BCA0: return "SHORTHAND FORMAT LETTER OVERLAP";
		case 0x1BCA1: return "SHORTHAND FORMAT CONTINUING OVERLAP";
		case 0x1BCA2: return "SHORTHAND FORMAT DOWN STEP";
		case 0x1BCA3: return "SHORTHAND FORMAT UP STEP";
		case 0x1D173: return "MUSICAL SYMBOL BEGIN BEAM";
		case 0x1D174: return "MUSICAL SYMBOL END BEAM";
		case 0x1D175: return "MUSICAL SYMBOL BEGIN TIE";
		case 0x1D176: return "MUSICAL SYMBOL END TIE";
		case 0x1D177: return "MUSICAL SYMBOL BEGIN SLUR";
		case 0x1D178: return "MUSICAL SYMBOL END SLUR";
		case 0x1D179: return "MUSICAL SYMBOL BEGIN PHRASE";
		case 0x1D17A: return "MUSICAL SYMBOL END PHRASE";
		case 0x01C0: return "LATIN LETTER DENTAL CLICK";
		case 0x01C1: return "LATIN LETTER LATERAL CLICK";
		case 0x01C2: return "LATIN LETTER ALVEOLAR CLICK";
		case 0x01C3: return "LATIN LETTER RETROFLEX CLICK";
		case 0x02B9: return "MODIFIER LETTER PRIME";
		case 0x02BA: return "MODIFIER LETTER DOUBLE PRIME";
		case 0x02BB: return "MODIFIER LETTER TURNED COMMA";
		case 0x02BC: return "MODIFIER LETTER APOSTROPHE";
		case 0x02BD: return "MODIFIER LETTER REVERSED COMMA";
		case 0x02C6: return "MODIFIER LETTER CIRCUMFLEX ACCENT";
		case 0x02C8: return "MODIFIER LETTER VERTICAL LINE";
		case 0x02C9: return "MODIFIER LETTER MACRON";
		case 0x02CA: return "MODIFIER LETTER ACUTE ACCENT";
		case 0x02CB: return "MODIFIER LETTER GRAVE ACCENT";
		case 0x02CC: return "MODIFIER LETTER LOW VERTICAL LINE";
		case 0x02CD: return "MODIFIER LETTER LOW MACRON";
		case 0x02D0: return "MODIFIER LETTER TRIANGULAR COLON";
		case 0x02D1: return "MODIFIER LETTER HALF TRIANGULAR COLON";
		case 0x02EE: return "MODIFIER LETTER DOUBLE APOSTROPHE";
		case 0xA4F8: return "LISU LETTER TONE MYA TI";
		case 0xA4F9: return "LISU LETTER TONE NA PO";
		case 0xA4FA: return "LISU LETTER TONE MYA CYA";
		case 0xA4FB: return "LISU LETTER TONE MYA BO";
		case 0xA4FC: return "LISU LETTER TONE MYA NA";
		case 0xA4FD: return "LISU LETTER TONE MYA JEU";
		case 0xA78F: return "LATIN LETTER SINOLOGICAL DOT";
		case 0x1427: return "CANADIAN SYLLABICS FINAL MIDDLE DOT";
		case 0x2D51: return "TIFINAGH LETTER TUAREG YANG";
		default: return null;
	}
}
/// describes a character for diagnostics, e.g. "'é' (U+00E9)" or "U+202E (RIGHT-TO-LEFT OVERRIDE)". Never includes misleading characters verbatim.
string describeChar(dchar c){
	if(auto name=charName(c)) return format("U+%04X (%s)",c,name);
	if(c<0x20||c==0x7F||isC1Control(c)||isDefaultIgnorable(c)||isWhite(c)||isMark(c)||!isGraphical(c)||!utf.isValidDchar(c)) return format("U+%04X",c);
	return format("'%s' (U+%04X)",c,c);
}
string describeChars(string s){
	import std.utf: byDchar;
	string r;
	foreach(dchar c;s.byDchar) r~=(r.length?" ":"")~describeChar(c);
	return r;
}
/// describes why `c` is not acceptable in code (outside comments and string literals).
string unsupportedCharMessage(dchar c){
	if(isBidiControl(c)) return format("bidirectional formatting character %s is not allowed",describeChar(c));
	if(isUnicodeLineBreak(c)) return format("unsupported character %s (only '\\n' and '\\r' are line breaks)",describeChar(c));
	if(c>=0x80&&isWhite(c)) return format("unsupported whitespace character %s (only ASCII whitespace is allowed)",describeChar(c));
	if(isDefaultIgnorable(c)) return format("unsupported character %s (invisible)",describeChar(c));
	return format("unsupported character %s",describeChar(c));
}
/// describes why `c` is not acceptable in comments and string literals.
string forbiddenInTextMessage(dchar c){
	if(isBidiControl(c)) return format("bidirectional formatting character %s is not allowed, not even in comments and string literals (use an escape sequence in a string literal if it is needed)",describeChar(c));
	if(isUnicodeLineBreak(c)) return format("character %s is not allowed, not even in comments and string literals (it may be displayed as a line break, but it is not one; use '\\n' or an escape sequence)",describeChar(c));
	return format("control character %s is not allowed, not even in comments and string literals (use an escape sequence in a string literal if it is needed)",describeChar(c));
}

private immutable {
string[2][] complexTokens =
	[["i",     "Identifier"                ],
	 ["@",     "Attribute"                 ],
	 ["``",    "StringLiteral"             ],
	 ["``c",   "StringLiteralC"            ],
	 ["``w",   "StringLiteralW"            ],
	 ["``d",   "StringLiteralD"            ],
	 ["''",    "CharacterLiteral"          ],
	 ["0",     "IntLiteral"                ],
	 ["0U",    "UintLiteral"               ],
	 ["0L",    "LongLiteral"               ],
	 ["0LU",   "UlongLiteral"              ],
	 [".0f",   "FloatLiteral"              ],
	 [".0",    "DoubleLiteral"             ],
	 [".0L",   "RealLiteral"               ],
	 [".0fi",  "ImaginaryFloatLiteral"     ],
	 [".0i",   "ImaginaryDoubleLiteral"    ],
	 [".0Li",  "ImaginaryLiteral"          ],
	 ["expected", "ExpectedComment"]];
string[2][] simpleTokens = 
	[["/",     "Divide"                    ],
	 ["/=",    "DivideEqual"               ],
	 [".",     "Dot"                       ],
	 ["..",    "DotDot"                    ],
	 ["...",   "DotDotDot"                 ],
	 ["&",     "And"                       ],
	 ["&=",    "AndEqual"                  ],
	 ["&&",    "AndAnd"                    ],
	 ["&&=",   "AndAndEqual"               ],
	 ["|",     "Or"                        ],
	 ["|=",    "OrEqual"                   ],
	 ["||",    "OrOr"                      ],
	 ["||=",   "OrOrEqual"                 ],
	 ["-",     "Minus"                     ],
	 ["-=",    "MinusEqual"                ],
	 ["--",    "MinusMinus"                ],
	 ["->",    "UglyMapsTo"                ],
	 ["+",     "Plus"                      ],
	 ["+=",    "PlusEqual"                 ],
	 ["++",    "PlusPlus"                  ],
	 ["<",     "Less"                      ],
	 ["<=",    "LessEqual"                 ],
	 ["<<",    "LeftShift"                 ],
	 ["<<=",   "LeftShiftEqual"            ],
	 ["<>",    "LessGreater"               ],
	 ["<>=",   "LessGreaterEqual"          ],
	 [">",     "Greater"                   ],
	 [">=",    "GreaterEqual"              ],
	 [">>=",   "RightShiftEqual"           ],
	 [">>>=",  "LogicalRightShiftEqual"    ],
	 [">>",    "RightShift"                ],
	 [">>>",   "LogicalRightShift"         ],
	 ["!",     "ExclamationMark"           ],
	 ["!=",    "NotEqual"                  ],
	 ["!<>",   "NotLessGreater"            ],
	 ["!<>=",  "Unordered"                 ],
	 ["!<",    "NotLess"                   ],
	 ["!<=",   "NotLessEqual"              ],
	 ["!>",    "NotGreater"                ],
	 ["!>=",   "NotGreaterEqual"           ],
	 ["(",     "LeftParen"                 ],
	 [")",     "RightParen"                ],
	 ["[",     "LeftBracket"               ],
	 ["]",     "RightBracket"              ],
	 ["{",     "LeftCurly"                 ],
	 ["}",     "RightCurly"                ],
	 ["?",     "QuestionMark"              ],
	 [",",     "Comma"                     ],
	 [";",     "Semicolon"                 ],
	 [":",     "Colon"                     ],
	 [":=",    "ColonEqual"                ],
	 ["$",     "Dollar"                    ],
	 ["=",     "Equal"                     ],
	 ["=>",    "UglyGoesTo"                ],
	 ["==",    "EqualEqual"                ],
	 ["*",     "Star"                      ],
	 ["*=",    "MultiplyEqual"             ],
	 ["%",     "Modulo"                    ],
	 ["%=",    "ModuloEqual"               ],
	 ["^",     "Pow"                       ],
	 ["^=",    "PowEqual"                  ],
	 ["~",     "Concat"                    ],
	 ["~=",    "ConcatEqual"              ]];
string[2][] unicodeTokens =
	[["·",     "Multiply2"                 ],
	 ["·=",    "MultiplyEqual2"            ],
	 ["⊥",     "Bottom",                   ],
	 ["⊤",     "Top",                      ],
	 ["¬",     "Negate",                   ],
	 ["∧",     "And2",                     ],
	 ["∧=",    "AndEqual2",                ],
	 ["∧←",    "AndAssign2"                ],
	 ["⊕",     "Xorb"                      ],
	 ["⊕=",    "XorbEqual"                 ],
	 ["⊕←",    "XorbAssign"                ],
	 ["⊻",     "Xor2"                      ],
	 ["⊻=",    "XorEqual2"                 ],
	 ["⊻←",    "XorAssign2"                ],
	 ["∨",     "Or2",                      ],
	 ["∨=",    "OrEqual2",                 ],
	 ["∨←",    "OrAssign2",                ],
	 ["≠",     "NotEqual2"                 ],
	 ["≤",     "LessEqual2"                ],
	 ["≥",     "GreaterEqual2"             ],
	 ["!≤",    "NotLessEqual2"             ],
	 ["!≥",    "NotGreaterEqual2"          ],
	 ["×",     "Times"                     ],
	 ["→",     "To"                        ],
	 ["⇒",     "GoesTo"                    ],
	 ["↦",     "MapsTo"                    ],
	 ["←",     "Assign",                   ],
	 ["/←",    "DivideAssign"              ],
	 ["&←",    "AndAssign"                 ],
	 ["&&←",   "AndAndAssign"              ],
	 ["|←",    "OrAssign"                  ],
	 ["||←",   "OrOrAssign"                ],
	 ["-←",    "MinusAssign"               ],
	 ["+←",    "PlusAssign"                ],
	 ["<<←",   "LeftShiftAssign"           ],
	 [">>←",   "RightShiftAssign"          ],
	 [">>>←",  "LogicalRightShiftAssign"   ],
	 ["*←",    "MultiplyAssign"            ],
	 ["·←",    "MultiplyAssign2"           ],
	 ["%←",    "ModuloAssign"              ],
	 ["^←",    "PowAssign"                 ],
	 ["~←",    "ConcatAssign"              ],
	 ["div←",  "IntegerDivisionAssign"     ],
	 ["sub←",  "NaturalMinusAssign"        ]];
string[2][] specialTokens = 
	[["",      "None",                     ],
	 [" ",     "Whitespace",               ],
	 ["//",    "Comment",                  ],
	 ["///",   "DokComment",               ],
	 ["\n",    "NewLine",                  ], // TODO: incorporate unicode new line support
	 ["Error", "Error"                     ],
	 ["__error","ErrorLiteral"             ],
	 ["div",   "IntegerDivision"           ],
	 ["div=",  "IntegerDivisionEqual"      ],
	 ["sub",   "NaturalMinus"              ],
	 ["sub=",  "NaturalMinusEqual"         ],
	 ["EOF",   "Eof"                       ]];


string[2][] compoundTokens = [];

string[] commonKeywords = ["dat","def","true","false","if","then","else","observe","assert","return","repeat","for","while","in","cobserve","import","Π","Pi","∏","cprod","as","coerce","pun","forget","typeof","_","wild","let"];
string[] psiKeywords = ["pure"];
string[] silqKeywords = ["λ","lambda","quantum","const","moved","once","spent","lifted","qfree","mfree","classical","do","with"];

string[] keywords = commonKeywords~(language==psi?psiKeywords:[])~(language==silq?silqKeywords:[]);

string[2][] tokens = specialTokens ~ complexTokens ~ simpleTokens ~ unicodeTokens ~ compoundTokens ~ keywordTokens(commonKeywords~psiKeywords~silqKeywords);
}

private{
auto keywordTokens(immutable(string)[] allKeywords){
	immutable(string[2])[] r;
	foreach(i,kw;allKeywords){
		if(kw=="∏") r~=[kw,"ucprod_"];
		else r~=[kw,kw~"_"];
	}
	return r;
}

string TokenNames(){
	string r;
	foreach(t;tokens) r~=lowerf(t[1])~",";
	return r;
}

string TokImpl(){
	string r="static if(type==\""~tokens[0][0]~"\") alias TokenType."~lowerf(tokens[0][1])~" Tok;";
	foreach(t;tokens) r~="else static if(type==\""~t[0]~"\") alias TokenType."~lowerf(t[1])~" Tok;";
	r~="else static assert(0,\"unknown Token '\"~type~\"'\");";
	return r;
}

string TokCharsImpl(){
	string r="static if(type==TokenType."~lowerf(tokens[0][1])~") enum TokChars=\""~tokens[0][0]~"\";";
	foreach(t;tokens) r~="else static if(type==TokenType."~lowerf(t[1])~") enum TokChars=\""~t[0]~"\";";
	r~="else static assert(0,\"invalid TokenType \"~to!string(type));";
	return r;
}
}
string TokenTypeToString(TokenType type){
	return tokens[cast(int)type][0];
}

string toString(immutable(Token)[] a){string r;foreach(t;a) r~='['~t.toString()~']'; return r;}

class Source{
	immutable{
		string name;
		string code;
	}
	this(string name, string code)in{auto c=code;assert(c.length>=4&&!c[$-4]&&!c[$-3]&&!c[$-2]&&!c[$-1]);}do{ // four padding zero bytes required because of UTF{
		this.name = name;
		this.code = code[0..$-4]; // don't expose the padding zeros
		sources ~= this;
	}
	string getLineOf(string rep)in{assert(this is get(rep));}do{
		//if(!code.length) return code;
		string before=code.ptr[0..code.length+4][0..rep.ptr-code.ptr];
		string after =code.ptr[0..code.length+4][rep.ptr-code.ptr..$];
		immutable(char)* start=code.ptr, end=code.ptr+code.length;
		foreach_reverse(ref c; before) if(c=='\n'||c=='\r'){start = &c+1; break;}
		foreach(ref c; after) if(c=='\n'||c=='\r'){end = &c; break;}
		return start[0..end-start];
	}
	static Source get(string rep){
		foreach(x; sources) if(rep.ptr>=x.code.ptr && rep.ptr+rep.length<=x.code.ptr+x.code.length+4) return x;
		return null;
	}
	void dispose(){
		foreach(i,x; sources) if(x is this){
			swap(sources[i], sources[$-1]);
			sources=sources[0..$-1];
			sources.assumeSafeAppend();
			return;
		}
		assert(0);
	}
	private static Source[] sources;
}

struct Location{
	string rep;    // slice of the code representing the Location
	int line;      // line number at start of location

	// reference to the source the code belongs to
	@property Source source()const{
		auto src = Source.get(rep);
		assert(src, "source for `"~rep~"` not found!");
		return src;
	}
	Location to(const(Location) end)const{// in{assert(end.source is source);}do{
		// in{assert(rep.ptr<=end.rep.ptr);}do{ // requiring that is not robust enough
		if(rep.ptr>end.rep.ptr+end.rep.length) return cast()this;
		return Location(rep.ptr[0..end.rep.ptr-rep.ptr+end.rep.length],line);
	}
	string toString(){
		if(!rep) return "<??>";
		return format("%s:%s <%s>", source.name, line, rep);
	}

	// empty location pointing at end
	LocationInfo info(int tabsize) {
		if(!line) return LocationInfo.init;
		LocationInfo r;
		r.source = source();

		r.startByte = cast(int)(rep.ptr - source.code.ptr);

		string l = source.getLineOf(rep);
		r.startLine = line;
		r.startColumn = rep.ptr-l.ptr<l.length ? displayWidth(l[0..rep.ptr-l.ptr], tabsize) : displayWidth(l, tabsize);

		r.endByte = r.startByte + cast(int)rep.length;
		auto n = cast(int)rep.representation.count('\n'); // (byte-wise: rep may contain invalid UTF-8)
		r.endLine = r.startLine + n;
		string lastRep = rep;
		if(n != 0) {
			import std.range: retro;
			auto afterLastNl = rep.representation.retro.countUntil('\n'); // number of bytes after the last '\n'
			lastRep = rep[$-afterLastNl..$];
			l= source.getLineOf(lastRep);
		}
		r.endColumn = displayWidth(l[0..min($, lastRep.ptr + lastRep.length - l.ptr)], tabsize) - 1;
		return r;
	}
}

struct LocationInfo {
	Source source;
	int startByte;
	int startLine;
	int startColumn;
	int endByte;
	int endLine;
	int endColumn;
}

struct Token{
	TokenType type;
	string toString() const{
		if(type == Tok!"EOF") return "EOF";
		if(loc.rep.length) return loc.rep;
		// TODO: remove boilerplate
		// TODO: get better representations
		switch(type){
			case Tok!"i":
				return name;
			case Tok!"@":
				return "@"~name;
			case Tok!"``":
				return '"'~escape(str)~'"';
			case Tok!"``c":
				return '"'~escape(str)~`"c`;
			case Tok!"``w":
				return '"'~escape(str)~`"w`;
			case Tok!"``d":
				return '"'~escape(str)~`"d`;
			case Tok!"''":
				return '\''~escape(to!string(cast(dchar)int64),false)~'\'';
			case Tok!"0", Tok!"0U":
			case Tok!"0L", Tok!"0LU":
			case Tok!".0f", Tok!".0", Tok!".0L":
			case Tok!".0i", Tok!".0fi", Tok!".0Li":
				return str;
			case Tok!"Error":
				return "error: "~str;
			case Tok!"true": return "true";
			case Tok!"false": return "false";
			default:
				return tokens[cast(int)type][0];
		}
	}
	union{
		string str, name;  // string literals, identifiers
		ulong int64;       // integer literals
	}
	Location loc;
}
template token(string t){enum token=Token(Tok!t);} // unions not yet supported

string caseSimpleToken(string prefix="", bool needs = false)pure{
	string r;
	int c=0,d=0;
	foreach(i;simpleTokens){string s=i[0]; if(s.startsWith(prefix)) c++;}
	if(c==1) r~=`res[0].type = Tok!"`~prefix~'"'~";\nbreak;\n";
	else{
		if(needs) r~="switch(*p++){\n";
		foreach(i;simpleTokens){
			string s = i[0]; if(s[0]=='/' || s[0] == '.' || s=="×") continue; // / can be the start of a comment, . could be the start of a float literal
			if(s.startsWith(prefix) && s.length==prefix.length+1){
				r~=`case '`~s[$-1]~"':\n";
				r~=caseSimpleToken(s,true);
			}
		}
		// TODO: this hacky and inefficient
		auto special=unicodeTokens.map!(x=>x[0]).filter!(x=>x.startsWith(prefix)&&x.length>prefix.length&&x[prefix.length]>0x80);
		if(!special.empty){
			r~="// "~text(special)~"\n";
			r~=`
				case 0x80: .. case 0xFF:
					len=0; p--;
					try{auto ch=utf.decode(p[0..4],len);
						switch(ch){
							enum uniStart = unicodeTokens[].map!(x=>x[0].to!(dchar[])).filter!(x=>x.length&&x[0]>=0x80).map!(x=>x[0]).array.sort.uniq.array;
							static foreach(x;uniStart){
								case x:
									enum candidates=unicodeTokens.map!(x=>x[0].idup).filter!(y=>y.startsWith("`~prefix~`"~text(x))).array.sort!"a.length>b.length";
									static if(candidates.length==1){
										res[0].type=Tok!(candidates[0]);
										p+=len;
										break Lswitch;
									}else {
										static foreach(y;candidates){ // TODO: get rid of linear search?
											if(p[0..y.length]==y){
											   res[0].type=Tok!y;
											   p+=y.length;
											   break Lswitch;
											}
										}
										goto default;
									}
							}
							default: break;
						}`~(prefix==""?`if(isAlphaEx(ch)){
							s=p, p+=len;
							if(auto why=identifierCharProblem(ch)){ errors~=tokError(format("character %s cannot be used in an identifier: %s",describeChar(ch),why),s[0..len]); continue; }
							goto identifier;
						}
						s=p, p+=len;
						if(ch==0xFEFF&&s==source.code.ptr) continue; // (UTF-8 byte order mark at the start of the file)
						errors~=tokError(unsupportedCharMessage(ch),s[0..len]); // (this includes all non-ASCII whitespace)
						continue;`:`res[0].type = Tok!"`~prefix~`"; break;`)~`

					}catch(Exception){
						// invalid UTF-8 sequence at p (p already points at its first byte, see above)
						`~(prefix==""?`invCharSeq(); continue;`:`res[0].type = Tok!"`~prefix~`"; break;`)~`
					}`;
		}
		if(needs) r~=`default: p--; res[0].type = Tok!"`~prefix~`"`~";\nbreak;\n}\nbreak;\n";
	}
	return r;
}

auto lex(Source source){ // pure
	return Lexer(source);
}

struct Anchor{
	size_t index;
}

struct Lexer{
	string code; // Manually allocated!
	immutable(char)* eof; // address of the first padding byte (end of the source code)
	Token[] buffer;
	Token[] errors;
	Source source;
	size_t n,m; // start and end index in buffer
	size_t s,e; // global start and end index
	size_t numAnchors;  // number of existing anchors for this lexer
	size_t firstAnchor; // first local index that has to remain in buffer
	int line;
	/+invariant(){ // useless because DMD does not test the invariant at the proper time...
		assert(e-s == (m-n+buffer.length)%buffer.length); // relation between (s,e) and (n,m)
		assert(!(buffer.length&buffer.length-1)); // buffer size is always a power of two
		assert(numAnchors||firstAnchor==size_t.max);
	}+/
	//pure: phobos ...
	this(Source src){
		source = src;
		code = src.code.ptr[0..src.code.length+4]; // rely on 4 padding zero bytes
		eof = src.code.ptr+src.code.length;
		if(src.code.length > int.max){ // (LocationInfo uses int byte offsets)
			errors~=tokError("no support for sources exceeding 2GB",null);
			code = eof[0..4]; // lex only the padding, i.e., produce just an EOF token
		}
		enum initsize=4096;//685438;//
		buffer = new Token[](initsize);//
		//buffer = (cast(Token*)malloc(Token.sizeof*initsize))[0..initsize];//
		numAnchors=0;
		firstAnchor=size_t.max;
		line=1;
		n=s=0;
		e=lexTo(buffer);
		m=e&buffer.length-1;
	}
	@property ref const(Token) front()const{return buffer[n];}
	@property bool empty(){return buffer[n].type==Tok!"EOF";}
	void popFront(){
		assert(!empty,"attempted to popFront empty lexer.");
		n = n+1 & buffer.length-1; s++;
		if(s<e) return; // if the buffer still contains elements
		assert(s==e && n==m);
		if(!numAnchors){// no anchors, that is easy, just reuse the whole buffer
			buffer[0]=buffer[n-1&buffer.length-1]; // we want at least one token of lookback, for nice error reporting
			e+=m=lexTo(buffer[n=1..$]);
			m=m+1&buffer.length-1;
			return;
		}
		assert(firstAnchor<buffer.length);
		size_t num;
		if(m < firstAnchor){ // there is an anchor but still space
			num=lexTo(buffer[n..firstAnchor]);
			e+=num; m=m+num&buffer.length-1;
			return;
		}else if(m > firstAnchor){ // ditto
			num=lexTo(buffer[m..$]);
			if(firstAnchor) num+=lexTo(buffer[0..firstAnchor]);
			e+=num; m=m+num&buffer.length-1;
			return;
		}
		auto len=buffer.length;
		buffer.length=len<<1; // double buffer size
		//buffer=(cast(Token*)realloc(buffer.ptr,(len<<1)*Token.sizeof))[0..len<<1];
		n=len+firstAnchor; // move start and firstAnchor
		buffer[len..n]=buffer[0..firstAnchor]; // move tokens to respect the new buffer topology
		num=0;
		if(n<buffer.length){
			num=lexTo(buffer[n..$]);
			e+=num; m=n+num&buffer.length-1;
		}	
		if(!m&&firstAnchor){
			num=lexTo(buffer[0..firstAnchor]);
			e+=num; m=num&buffer.length-1;
		}
	}
	Anchor pushAnchor(){
		if(!numAnchors) firstAnchor=n;
		numAnchors++;
		return Anchor(s);
	}
	void popAnchor(Anchor anchor){
		numAnchors--;
		if(!numAnchors) firstAnchor=size_t.max;
		n=n+anchor.index-s&buffer.length-1;
		s=anchor.index;
	}

private:
	Token tokError(string s, string rep, int l=0){
		auto r = token!"Error";
		r.str = s;
		r.loc = Location(rep, l?l:line);
		return r;
	}

	size_t lexTo(Token[] res)in{assert(res.length);}do{
		import std.array: appender;
		if(code.length<=4){ // only padding left: keep producing EOF tokens without consuming anything
			res[0].type = Tok!"EOF";
			res[0].loc.rep=(eof+1)[0..1];
			res[0].loc.line = line;
			return 1;
		}
		auto p=code.ptr;
		auto s=p;    // used if the input has to be sliced
		auto sl=line;// ditto
		char del;    // used if a delimiter of some sort needs to be remembered
		size_t len;  // used as a temporary that stores the length of the last UTF sequence
		size_t num=0;// number of tokens lexed, return value
		typeof(p) invCharSeq_l=null;
		size_t invCharSeq_e=size_t.max; // index of the error that covers the byte at invCharSeq_l
		void invCharSeq(){ // report the byte at p as part of an invalid UTF-8 sequence, merge runs of such bytes into one error
			if(invCharSeq_e<errors.length && p==invCharSeq_l+1) errors[invCharSeq_e].loc.rep=errors[invCharSeq_e].loc.rep.ptr[0..errors[invCharSeq_e].loc.rep.length+1];
			else{ invCharSeq_e=errors.length; errors~=tokError("invalid UTF-8 sequence",p[0..1]); }
			invCharSeq_l=p; p++;
		}
		bool atEof(){ return p>=eof; } // (p never passes eof except in the EOF case below)
		// text macros:
		void textChar(dchar ch,immutable(char)* at,size_t len){ // check a character inside a comment or string literal
			if(isForbiddenInText(ch)) errors~=tokError(forbiddenInTextMessage(ch),at[0..len]);
		}
		enum skipUnicode = q{if(*p<0x80){p++;break;} len=0; try{textChar(utf.decode(p[0..4],len),p,len); p+=len;} catch(Exception){invCharSeq();}};
		enum skipUnicodeCont = q{if(*p<0x80){p++;continue;} len=0; try{textChar(utf.decode(p[0..4],len),p,len); p+=len;} catch(Exception){invCharSeq();}}; // don't break, continue
		enum caseNl = q{case '\r':  if(p[1]=='\n') p++; goto case; case '\n': line++; p++; continue;};
		loop: while(res.length) { // breaks on EOF or buffer full
			auto begin=p; // start of a token's representation
			auto sline=line;
		Lswitch:switch(*p++){
				// whitespace
				case 0, 0x1A:
					if(begin<eof){ // embedded NUL or SUB byte: do not silently truncate the file
						errors~=tokError(format("unsupported character %s",describeChar(*begin)),begin[0..1]);
						continue;
					}
					res[0].type = Tok!"EOF";
					res[0].loc.rep=p[0..1];
					res[0].loc.line = line; // TODO: Why is this necessary?
					res=res[1..$];
					num++;
					break loop;
				case ' ', '\t', '\v':
					continue;   // ignore whitespace
				case '\r': if(*p=='\n') p++; goto case;
				case '\n': line++;
					continue;

				// simple tokens
				mixin(caseSimpleToken());

				// slash is special
				case '/':
					switch(*p){
						case '=': res[0].type = Tok!"/="; p++;
							break;
						case '/': p++;
							// parse "expected" comments
							if(*p==' ') p++;
							bool isExp=true;
							foreach(char c;"expected:"){
								if(*p==c) p++;
								else{ isExp=false; break; }
							}
							auto cur=p;
							// end of parse "expected" comments
							while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont);
							if(isExp){
								res[0].type = Tok!"expected";
								res[0].str = cur[0..p-cur];
								break;
							}else continue; // ignore comment
						case '*':
							s=p++-1;
							sl=line;
							consumecom2: for(;;){
								switch(*p){
									mixin(caseNl); // handle newlines
									case '*': p++; if(*p=='/'){p++; break consumecom2;} break;
									case 0, 0x1A: errors~=tokError("unterminated /* */ comment",s[0..p-s],sl); break consumecom2;
									default: mixin(skipUnicode);
								}
							}
							continue; // ignore comment
						case '+':
							int d=1;
							s=p++-1;
							sl=line;
							consumecom3: while(d){
								switch(*p){
									mixin(caseNl); // handle newlines
									case '+':  p++; if(*p=='/') d--, p++; break;
									case '/':  p++; if(*p=='+') d++, p++; break;
									case 0, 0x1A: errors~=tokError("unterminated /+ +/ comment",s[0..p-s],sl); break consumecom3;
									default: mixin(skipUnicode);
								}
							}
							continue; // ignore comment
						default: res[0].type = Tok!"/"; break;
					}
					break;
				// dot is special
				case '.':
					if('0' > *p || *p > '9'){
						if(*p != '.')      res[0].type = Tok!".";
						else if(*++p!='.') res[0].type = Tok!"..";
						else               res[0].type = Tok!"...", p++;
						break;
					}
					goto case;
				// numeric literals
				case '0': .. case '9':
					res[0] = lexNumber(--p);
					if(res[0].type == Tok!"Error") errors~=res[0], res[0].type=Tok!"__error";
					break;
				// character literals
				case '\'':
					s = p; sl = line;
					res[0].type = Tok!"''";
					res[0].int64 = 0;
					if(*p=='\\'){
						try p++, res[0].int64 = cast(ulong)readEscapeSeq(p);
						catch(EscapeSeqException e) if(e.msg) errors~=tokError(e.msg,e.loc); else invCharSeq();
					}else if(*p=='\n'||*p=='\r'||*p==0||*p==0x1A){
						// newline or end of file: don't consume it, report below
					}else{
						try{
							len=0;
							res[0].int64 = utf.decode(p[0..4],len);
							textChar(cast(dchar)res[0].int64,p,len);
							p+=len;
						}catch(Exception){invCharSeq();}
					}
					if(*p!='\''){
						//while((*p!='\''||(p++,0)) && *p && *p!=0x1A) mixin(skipUnicodeCont);
						errors~=tokError("unterminated character constant",(s-1)[0..p-s+1],sl);
					}else p++;
					break;
				// string literals
				// WYSIWYG string/AWYSIWYG string
				case 'r':
					if(*p!='"') goto case 'R';
					p++; del='"';
					goto skipdel;
				case '`':
					del = '`'; skipdel:
					s = p; sl = line;
					readwysiwyg: for(;;){
						if(*p==del){p++; res[0].str = s[0..p-s-1]; break;} // reference to code
						switch(*p){
							mixin(caseNl); // handle newlines
							case 0, 0x1A:
								errors~=tokError("unterminated string literal", (s-1)[0..1],sl);
								res[0].str = s[0..p-s];
								break readwysiwyg;
							default: mixin(skipUnicode);
						}
					}
					res[0].type = Tok!"``";
					goto lexstringsuffix;
				// token string
				case 'q':
					if(*p=='"') goto delimitedstring;
					/+if(*p!='{') +/goto case 'Q';
					/+p++; s = p; sl = line;
					del = 0;
					readtstring: for(int nest=1;;){ // TODO: implement more efficiently
						Token tt;
						code=code[p-code.ptr..$]; // update code to allow recursion
						lexTo((&tt)[0..1]);
						p=code.ptr;
						switch(tt.type){
							case Tok!"EOF":
								errors~=tokError("unterminated token string literal", (s-2)[0..1], sl);
								break readtstring;
							case Tok!"{":  nest++; break;
							case Tok!"}":  nest--; if(!nest) break readtstring; break;
							default: break;
						}
					}
					res[0].type = Tok!"``";
					res[0].str = s[0..p-s-1]; // reference to code
					goto lexstringsuffix;+/
					delimitedstring:
					res[0].type = Tok!"``";
					res[0].str = null;
					s=++p; sl=line;
					switch(*p){
						case 'a': .. case 'z':
						case 'A': .. case 'Z':
							for(;;){
								switch(*p){
									case 'a': .. case 'z':
									case 'A': .. case 'Z':
									case '0': .. case '9':
										p++;
										continue;
									case 0x80: .. case 0xFF:
										len=0;
										try{auto ch=utf.decode(p[0..4],len);
											if(isIdentChar(ch)){p+=len; continue;}
											break;
										}catch(Exception){break;} // (reported below)
									default: break; // (includes newline and end of file)
								}
								break;
							}
							auto ident=s[0..p-s];
							if(*p!='\n' && *p!='\r') errors~=tokError("heredoc identifier must be followed by a new line",p[0..1]);
							while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont); // mere error handling
							if(*p=='\r'){line++;p++;if(*p=='\n') p++;}
							else if(*p=='\n'){line++;p++;}
							s=p;
							readheredoc: while((*p!=0) & (*p!=0x1A)){ // always at start of new line here
								for(auto ip=ident.ptr, end=ident.ptr+ident.length;;){
									if(ip==end){ if(*p=='"') break readheredoc; break; } // (a line merely starting with the identifier does not terminate the string)
									switch(*p){
										mixin(caseNl);
										case 0x80: .. case 0xFF:
											len=0;
											try{auto ch=utf.decode(p[0..4],len);
												if(isIdentChar(ch)){
													if(p[0..len]!=ip[0..len]) break;
													p+=len; ip+=len; continue;
												}
												break;
											}catch(Exception){invCharSeq(); break;}
										default: 
											if(*p!=*ip) break;
											p++; ip++; continue;
									}
									break;
								}
								while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont);
								if(*p=='\r'){line++;p++;if(*p=='\n') p++;}
								else if(*p=='\n'){line++;p++;}
							}
							res[0].str = p>s+ident.length?s[0..p-s-ident.length]:""; // reference to code
							if(*p!='"') errors~=tokError("unterminated heredoc string literal",(s-1)[0..1],sl);
							else p++;
							break;
						default:
							del=*p; char rdel=del; dchar ddel=0;
							switch(del){
								case '[': rdel=']'; s=++p; break;
								case '(': rdel=')'; s=++p; break;
								case '<': rdel='>'; s=++p; break;
								case '{': rdel='}'; s=++p; break;
								case 0, 0x1A: // end of file (or embedded NUL): do not consume
									errors~=tokError("unterminated delimited string literal",(s-2)[0..2],sl);
									goto lexstringsuffix;
								case '\r', '\n', ' ', '\t', '\v': // do not consume: lexed as whitespace afterwards
									errors~=tokError("string delimiter cannot be whitespace",p[0..1]);
									goto lexstringsuffix;
								case 0x80: .. case 0xFF:
									len=0;
									try{
										ddel=utf.decode(p[0..4],len);
										s=p+=len;
									}catch(Exception){
										invCharSeq();
										goto lexstringsuffix;
									}
									break;
								default: s=++p; break;
							}
							if(ddel){
								while((*p!=0) & (*p!=0x1A)){
									if(*p=='\r'){line++;p++;if(*p=='\n') p++; continue;}
									else if(*p=='\n'){line++;p++; continue;}
									else if(*p<0x80){p++; continue;}
									len=0;
									try{
										auto x=utf.decode(p[0..4],len);
										textChar(x,p,len);
										if(ddel==x){
											res[0].str = s[0..p-s]; // reference to code
											p+=len; break;
										}
										p+=len;
									}catch(Exception){invCharSeq();}
								}
							}else{
								int nest=1;
								for(;(nest!=0) & (*p!=0) & (*p!=0x1A);){
									if(*p=='\r'){line++;p++;if(*p=='\n') p++;}
									else if(*p=='\n'){line++;p++;}
									else if(*p==rdel){nest--; p++;}
									else if(*p==del){nest++; p++;}
									else if(*p & 0x80){
										len=0;
										try{
											textChar(utf.decode(p[0..4],len),p,len);
											p+=len;
										}catch(Exception){invCharSeq();}
									}else p++;
								}
								if(!nest) res[0].str = s[0..p-s-1]; // reference to code
								else res[0].str = s[0..p-s]; // (unterminated)
							}
							if(*p!='"'){
								if(*p) errors~=tokError("expected '\"' to close delimited string literal",p[0..1]);
								else errors~=tokError("unterminated delimited string literal",(s-2)[0..1],sl);
							}else p++;
							break;
					}
					goto lexstringsuffix;
				// Hex string
				case 'x':
					if(*p!='"') goto case 'X';
					auto r=appender!string(); p++; s=p; sl=line;
					readhexstring: for(int c=0,ch,d;;){ // c counts hex digits (not other characters)
						switch(*p){
							mixin(caseNl); // handle newlines
							case ' ', '\t', '\v': p++; break;
							case 0, 0x1A:
								errors~=tokError("unterminated hex string literal",(s-1)[0..1],sl);
								break readhexstring;
							case '0': .. case '9': d=*p-'0'; goto handlexchar;
							case 'a': .. case 'f': d=*p-('a'-0xa); goto handlexchar;
							case 'A': .. case 'F': d=*p-('A'-0xA); goto handlexchar;
							handlexchar:
								if(c&1) r.put(cast(char)(ch|d));
								else ch=d<<4;
								c++; p++;
								break;
							case '"':
								if(c&1) errors~=tokError(format("found %s character%s when expecting an even number of hex digits",toEngNum(c),c!=1?"s":""),s[0..p-s]);
								p++; break readhexstring;
							default:
								if(*p<128){
									errors~=tokError(format("found %s when expecting hex digit",describeChar(*p)),p[0..1]);
									p++;
								}else{
									len=0;
									try{
										auto chr = utf.decode(p[0..4],len);
										errors~=tokError(format("found %s when expecting hex digit",describeChar(chr)),p[0..len]);
										p+=len;
									}catch(Exception){invCharSeq();}
								}
								break;
						}
					}
					res[0].type = Tok!"``";
					res[0].str = r.data;
					goto lexstringsuffix;
				// DQString
				case '"':{
					// appender only used if there is an escape sequence, slice otherwise
					// TODO: how costly is eager initialization?
					auto r=appender!string();
					auto start = s = p; sl = line;
					bool terminated=false;
					readdqstring: for(;;){
						switch(*p){
							mixin(caseNl);
							case 0, 0x1A:
								errors~=tokError("unterminated string literal",(start-1)[0..1],sl); // (reported at the line of the opening quote)
								break readdqstring;
							case '\\':
								r.put(s[0..p++-s]);
								try r.put(readEscapeSeq(p));
								catch(EscapeSeqException e) if(e.msg) errors~=tokError(e.msg,e.loc); else invCharSeq();
								s = p;
								continue;
							case '"': p++; terminated=true; break readdqstring;
							default: mixin(skipUnicode);
						}
					}
					auto end = terminated ? p-1 : p; // (don't include the closing quote)
					res[0].type = Tok!"``";
					if(!r.data.length) res[0].str = start[0..end-start];
					else{ r.put(s[0..end-s]); res[0].str = r.data; }
					goto lexstringsuffix; }
					lexstringsuffix:
					if(*p=='c')      res[0].type = Tok!"``c", p++;
					else if(*p=='w') res[0].type = Tok!"``w", p++;
					else if(*p=='d') res[0].type = Tok!"``d", p++;
					break;
				case '@':
					s=p;
					readattrib: for(;;){
						switch(*p){
							case '_':
							case 'a': .. case 'z':
							case 'A': .. case 'Z':
							case '0': .. case '9':
								p++;
								break;
							case 0x80: .. case 0xFF:
								len=0;
								try if(isIdentChar(utf.decode(p[0..4],len))) p+=len;
									else break readattrib;
								catch(Exception){break readattrib;} // will be caught in the next iteration
								break;
							default: break readattrib;
						}
					}
					res[0].type=Tok!"@";
					// skip leading `@`
					res[0].name = s[0..p-s];
					break;
				// identifiers and keywords
				case '_':
				case 'a': .. case 'p': /*q, r*/ case 's': .. case 'w': /*x*/ case 'y', 'z':
				case 'A': .. case 'Z':
					s = p-1;
					identifier:
					readident: for(;;){
						switch(*p){
							case '_':
							case 'a': .. case 'z':
							case 'A': .. case 'Z':
							case '0': .. case '9':
								p++;
								break;
							case 0x80: .. case 0xFF:
								len=0;
								try if(isIdentChar(utf.decode(p[0..4],len))) p+=len;
									else break readident;
								catch(Exception){break readident;} // will be caught in the next iteration
								break;
							default: break readident;
						}
					}
					while(*p=='\'') ++p; // support primed identifiers
					res[0].name = s[0..p-s];
					res[0].type=isKeyword(res[0].name);
					break;
				case '#':{ // (e.g., a comment in Python: then the rest of the line is skipped)
					auto q=begin;
					while(q>source.code.ptr&&(q[-1]==' '||q[-1]=='\t')) q--;
					if(!(q==source.code.ptr||q[-1]=='\n'||q[-1]=='\r'||among(*p,' ','\t','!','\n','\r','\0'))) goto default; // (likely not a comment)
					errors~=tokError("unsupported character '#'",begin[0..1]);
					while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont);
					continue;
				}
				default: // unsupported ASCII character (control characters, '\\', '#', ...); already consumed
					errors~=tokError(format("unsupported character %s",describeChar(*begin)),begin[0..1]);
					continue;
			}
			res[0].loc.rep=begin[0..p-begin];
			res[0].loc.line=sline;
			res=res[1..$];
			num++;
		}
		code=code[p-code.ptr..$];
		return num;
	}
	
	private Token lexNumber(ref immutable(char)* p){
		auto s = p;
		static bool isDec(char c)=>'0'<=c&&c<='9';
		static bool isBin(char c)=>c=='0'||c=='1';
		static bool isOct(char c)=>'0'<=c&&c<='7';
		static bool isHex(char c)=>'0'<=c&&c<='9'||'a'<=c&&c<='f'||'A'<=c&&c<='F';
		bool isPrefixed=false,isFloat=false,isImag=false;
		if(*p == '0'){
			auto q = p + 1;
			if(*q=='b'||*q=='B'){
				isPrefixed=true,p+=2;
				while(isBin(*p)) p++;
			}else if(*q=='o'||*q=='O'){
				isPrefixed=true,p+=2;
				while(isOct(*p)) p++;
			}else if(*q=='x'||*q=='X'){
				isPrefixed=true,p+=2;
				while(isHex(*p)) p++;
			}
			if(isPrefixed&&p==s+2) return tokError("missing digits after base prefix",s[0..p-s]);
		}
		if(!isPrefixed){
			while(isDec(*p)) p++;
			if(*p=='.'&&*(p+1)!='.'){
				isFloat=true,p++;
				while(isDec(*p)) p++;
			}
			if(*p=='e'||*p=='E'){
				auto q=p+1;
				if(*q=='+'||*q=='-') q++;
				if(isDec(*q)){
					isFloat=true;
					long exp=0;
					for(p=q;isDec(*p);p++)
						if(exp<=int.max) exp=10*exp+(*p-'0');
					if(exp>int.max) errors~=tokError("exponent too large",s[0..p-s]);
				}
			}
			if(*p=='i') isFloat=isImag=true,p++;
		}
		Token r;
		r.type=isImag?Tok!".0i":isFloat?Tok!".0":Tok!"0";
		r.str=s[0..p-s];
		return r;
	}
}

// Exception thrown on unrecognized escape sequences
private class EscapeSeqException: Exception{string loc; this(string msg,string loc){this.loc=loc;super(msg);}}

/* Reads an escape sequence and increases the given pointer to point past the sequence
	returns a dchar representing the read escape sequence or
	throws EscapeSeqException if the input is not well formed
 */
private dchar readEscapeSeq(ref immutable(char)* _p) in{assert(*(_p-1)=='\\');}do{ // pure
	auto p=_p;
	switch(*p){
		case '\'','\?','"','\\':
			_p=p+1; return *p;
		case 'a': _p=p+1; return '\a';
		case 'b': _p=p+1; return '\b';
		case 'f': _p=p+1; return '\f';
		case 'n': _p=p+1; return '\n';
		case 'r': _p=p+1; return '\r';
		case 't': _p=p+1; return '\t';
		case 'v': _p=p+1; return '\v';
		case '0': .. case '7': // BUG: Actually works for all extended ASCII characters
			auto s=p;
			for(int r=*p++-'0', i=0;;i++, r=(r<<3)+*p++-'0')
				if(i>2||'0'>*p||*p>'7'){
					_p=p; if(r>255) throw new EscapeSeqException(format("escape sequence '\\%s' exceeds ubyte.max",s[0..p-s]),(s-1)[0..p-s+1]);
					return cast(dchar)r;
				}
		case 'x', 'u', 'U':
			auto s=p;
			int numh;
			if(*p=='x'){
				p++;
				numh=2;
			}else if(*p++=='u') numh=4;
			else numh=8;
			int r;
			foreach(i,x;p[0..numh]){
				switch(x){
					case '0': .. case '9': r=r<<4 | x-'0'; break;
					case 'a': .. case 'f': r=r<<4 | x-('a'-0xa); break;
					case 'A': .. case 'F': r=r<<4 | x-('A'-0xA); break;
					default:
						_p=p;
						throw new EscapeSeqException(format("escape hex sequence has %s digit%s instead of %s",
						                                    toEngNum(cast(uint)i),(i!=1?"s":""),toEngNum(numh)),(_p-1)[0..p-_p+1]);
				}
				p++;
			}
			_p=p;
			if(!utf.isValidDchar(cast(dchar)r)) throw new EscapeSeqException(format("invalid UTF character '\\%s'",s[0..p-s]),(s-1)[0..p-s+1]);
			return cast(dchar)r;
		case 0, 0x1A, '\n', '\r': // end of file or line: do not consume
			_p=p; throw new EscapeSeqException("unterminated escape sequence",(p-1)[0..1]);
		default:
			if(*p<128){_p=p+1; throw new EscapeSeqException(format("unrecognized escape sequence '\\' followed by %s",describeChar(*p)),p[0..1]);}
			else{
				auto s=p;
				size_t len=0;
				dchar ch;
				try{
					ch=utf.decode(p[0..4],len);
					p+=len;
				}catch(Exception){throw new EscapeSeqException(null,p[0..1]);}
				_p=p; throw new EscapeSeqException(format("unrecognized escape sequence '\\' followed by %s",describeChar(ch)),s[0..len]);
			}
	}
}

private string isKw(string[] cases){
	string r="switch(s){";
	foreach(x;cases) r~=`case "`~x~`": return Tok!"`~x~`";`;
	return r~="default: break;}";
}
TokenType isKeyword(string s){
	switch(s){
		static foreach(t;keywords)
		case t: return Tok!t;
		default: break;
	}
	return Tok!"i";
}
