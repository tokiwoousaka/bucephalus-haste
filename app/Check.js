"use strict";
// This object will hold all exports.
var Haste = {};

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(self, other), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1,_2){return E(_1)==E(_2);},_3=function(_4,_5){return E(_4)!=E(_5);},_6=new T2(0,_0,_3),_7=function(_8,_9){var _a=E(_8),_b=E(_9);return (_a>_b)?E(_a):E(_b);},_c=function(_d,_e){var _f=E(_d),_g=E(_e);return (_f>_g)?E(_g):E(_f);},_h=function(_i,_j){return (_i>=_j)?(_i!=_j)?2:1:0;},_k=function(_l,_m){return new F(function(){return _h(E(_l),E(_m));});},_n=function(_o,_p){return E(_o)>=E(_p);},_q=function(_r,_s){return E(_r)>E(_s);},_t=function(_u,_v){return E(_u)<=E(_v);},_w=function(_x,_y){return E(_x)<E(_y);},_z={_:0,a:_6,b:_k,c:_w,d:_t,e:_q,f:_n,g:_7,h:_c},_A=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_B=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_C=function(_D,_E,_){var _F=B(A1(_D,_)),_G=B(A1(_E,_));return _F;},_H=function(_I,_J,_){var _K=B(A1(_I,_)),_L=B(A1(_J,_));return new T(function(){return B(A1(_K,_L));});},_M=function(_N,_O,_){var _P=B(A1(_O,_));return _N;},_Q=function(_R,_S,_){var _T=B(A1(_S,_));return new T(function(){return B(A1(_R,_T));});},_U=new T2(0,_Q,_M),_V=function(_W,_){return _W;},_X=function(_Y,_Z,_){var _10=B(A1(_Y,_));return new F(function(){return A1(_Z,_);});},_11=new T5(0,_U,_V,_H,_X,_C),_12=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_13=new T(function(){return B(unCStr("base"));}),_14=new T(function(){return B(unCStr("IOException"));}),_15=__Z,_16=new T(function(){var _17=hs_wordToWord64(new Long(4053623282,1685460941,true)),_18=hs_wordToWord64(new Long(3693590983,2507416641,true));return new T5(0,_17,_18,new T5(0,_17,_18,_13,_12,_14),_15,_15);}),_19=function(_1a){return E(_16);},_1b=function(_1c){return E(E(_1c).a);},_1d=function(_1e,_1f,_1g){var _1h=B(A1(_1e,_)),_1i=B(A1(_1f,_)),_1j=hs_eqWord64(_1h.a,_1i.a);if(!_1j){return __Z;}else{var _1k=hs_eqWord64(_1h.b,_1i.b);return (!_1k)?__Z:new T1(1,_1g);}},_1l=function(_1m){var _1n=E(_1m);return new F(function(){return _1d(B(_1b(_1n.a)),_19,_1n.b);});},_1o=new T(function(){return B(unCStr(": "));}),_1p=new T(function(){return B(unCStr(")"));}),_1q=new T(function(){return B(unCStr(" ("));}),_1r=function(_1s,_1t){var _1u=E(_1s);return (_1u._==0)?E(_1t):new T2(1,_1u.a,new T(function(){return B(_1r(_1u.b,_1t));}));},_1v=new T(function(){return B(unCStr("interrupted"));}),_1w=new T(function(){return B(unCStr("system error"));}),_1x=new T(function(){return B(unCStr("unsatisified constraints"));}),_1y=new T(function(){return B(unCStr("user error"));}),_1z=new T(function(){return B(unCStr("permission denied"));}),_1A=new T(function(){return B(unCStr("illegal operation"));}),_1B=new T(function(){return B(unCStr("end of file"));}),_1C=new T(function(){return B(unCStr("resource exhausted"));}),_1D=new T(function(){return B(unCStr("resource busy"));}),_1E=new T(function(){return B(unCStr("does not exist"));}),_1F=new T(function(){return B(unCStr("already exists"));}),_1G=new T(function(){return B(unCStr("resource vanished"));}),_1H=new T(function(){return B(unCStr("timeout"));}),_1I=new T(function(){return B(unCStr("unsupported operation"));}),_1J=new T(function(){return B(unCStr("hardware fault"));}),_1K=new T(function(){return B(unCStr("inappropriate type"));}),_1L=new T(function(){return B(unCStr("invalid argument"));}),_1M=new T(function(){return B(unCStr("failed"));}),_1N=new T(function(){return B(unCStr("protocol error"));}),_1O=function(_1P,_1Q){switch(E(_1P)){case 0:return new F(function(){return _1r(_1F,_1Q);});break;case 1:return new F(function(){return _1r(_1E,_1Q);});break;case 2:return new F(function(){return _1r(_1D,_1Q);});break;case 3:return new F(function(){return _1r(_1C,_1Q);});break;case 4:return new F(function(){return _1r(_1B,_1Q);});break;case 5:return new F(function(){return _1r(_1A,_1Q);});break;case 6:return new F(function(){return _1r(_1z,_1Q);});break;case 7:return new F(function(){return _1r(_1y,_1Q);});break;case 8:return new F(function(){return _1r(_1x,_1Q);});break;case 9:return new F(function(){return _1r(_1w,_1Q);});break;case 10:return new F(function(){return _1r(_1N,_1Q);});break;case 11:return new F(function(){return _1r(_1M,_1Q);});break;case 12:return new F(function(){return _1r(_1L,_1Q);});break;case 13:return new F(function(){return _1r(_1K,_1Q);});break;case 14:return new F(function(){return _1r(_1J,_1Q);});break;case 15:return new F(function(){return _1r(_1I,_1Q);});break;case 16:return new F(function(){return _1r(_1H,_1Q);});break;case 17:return new F(function(){return _1r(_1G,_1Q);});break;default:return new F(function(){return _1r(_1v,_1Q);});}},_1R=new T(function(){return B(unCStr("}"));}),_1S=new T(function(){return B(unCStr("{handle: "));}),_1T=function(_1U,_1V,_1W,_1X,_1Y,_1Z){var _20=new T(function(){var _21=new T(function(){var _22=new T(function(){var _23=E(_1X);if(!_23._){return E(_1Z);}else{var _24=new T(function(){return B(_1r(_23,new T(function(){return B(_1r(_1p,_1Z));},1)));},1);return B(_1r(_1q,_24));}},1);return B(_1O(_1V,_22));}),_25=E(_1W);if(!_25._){return E(_21);}else{return B(_1r(_25,new T(function(){return B(_1r(_1o,_21));},1)));}}),_26=E(_1Y);if(!_26._){var _27=E(_1U);if(!_27._){return E(_20);}else{var _28=E(_27.a);if(!_28._){var _29=new T(function(){var _2a=new T(function(){return B(_1r(_1R,new T(function(){return B(_1r(_1o,_20));},1)));},1);return B(_1r(_28.a,_2a));},1);return new F(function(){return _1r(_1S,_29);});}else{var _2b=new T(function(){var _2c=new T(function(){return B(_1r(_1R,new T(function(){return B(_1r(_1o,_20));},1)));},1);return B(_1r(_28.a,_2c));},1);return new F(function(){return _1r(_1S,_2b);});}}}else{return new F(function(){return _1r(_26.a,new T(function(){return B(_1r(_1o,_20));},1));});}},_2d=function(_2e){var _2f=E(_2e);return new F(function(){return _1T(_2f.a,_2f.b,_2f.c,_2f.d,_2f.f,_15);});},_2g=function(_2h){return new T2(0,_2i,_2h);},_2j=function(_2k,_2l,_2m){var _2n=E(_2l);return new F(function(){return _1T(_2n.a,_2n.b,_2n.c,_2n.d,_2n.f,_2m);});},_2o=function(_2p,_2q){var _2r=E(_2p);return new F(function(){return _1T(_2r.a,_2r.b,_2r.c,_2r.d,_2r.f,_2q);});},_2s=44,_2t=93,_2u=91,_2v=function(_2w,_2x,_2y){var _2z=E(_2x);if(!_2z._){return new F(function(){return unAppCStr("[]",_2y);});}else{var _2A=new T(function(){var _2B=new T(function(){var _2C=function(_2D){var _2E=E(_2D);if(!_2E._){return E(new T2(1,_2t,_2y));}else{var _2F=new T(function(){return B(A2(_2w,_2E.a,new T(function(){return B(_2C(_2E.b));})));});return new T2(1,_2s,_2F);}};return B(_2C(_2z.b));});return B(A2(_2w,_2z.a,_2B));});return new T2(1,_2u,_2A);}},_2G=function(_2H,_2I){return new F(function(){return _2v(_2o,_2H,_2I);});},_2J=new T3(0,_2j,_2d,_2G),_2i=new T(function(){return new T5(0,_19,_2J,_2g,_1l,_2d);}),_2K=new T(function(){return E(_2i);}),_2L=function(_2M){return E(E(_2M).c);},_2N=__Z,_2O=7,_2P=function(_2Q){return new T6(0,_2N,_2O,_15,_2Q,_2N,_2N);},_2R=function(_2S,_){var _2T=new T(function(){return B(A2(_2L,_2K,new T(function(){return B(A1(_2P,_2S));})));});return new F(function(){return die(_2T);});},_2U=function(_2V,_){return new F(function(){return _2R(_2V,_);});},_2W=function(_2X){return new F(function(){return A1(_2U,_2X);});},_2Y=function(_2Z,_30,_){var _31=B(A1(_2Z,_));return new F(function(){return A2(_30,_31,_);});},_32=new T5(0,_11,_2Y,_X,_V,_2W),_33=function(_34){return E(_34);},_35=new T2(0,_32,_33),_36=new T2(0,_35,_V),_37=0,_38=function(_39,_3a,_){while(1){var _3b=E(_39);if(!_3b._){return _37;}else{var _3c=B(A2(_3b.a,_3a,_));_39=_3b.b;continue;}}},_3d=new T(function(){return eval("(function(e){e.width = e.width;})");}),_3e=new T1(0,33),_3f=function(_3g,_3h,_3i){return new T3(0,E(_3g),E(_3h),E(_3i));},_3j=function(_3k,_3l,_3m,_3n){return new T4(1,E(_3k),E(_3l),E(_3m),E(_3n));},_3o=function(_){return _37;},_3p=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_3q=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_3r=function(_3s,_3t,_){var _3u=__app1(E(_3p),_3t),_3v=B(A2(_3s,_3t,_)),_3w=__app1(E(_3q),_3t);return new F(function(){return _3o(_);});},_3x=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_3y=function(_3z,_3A,_){var _3B=__app1(E(_3p),_3A),_3C=B(A2(_3z,_3A,_)),_3D=__app1(E(_3x),_3A);return new F(function(){return _3o(_);});},_3E=function(_3F,_){return _37;},_3G=",",_3H="rgba(",_3I=new T(function(){return toJSStr(_15);}),_3J="rgb(",_3K=")",_3L=new T2(1,_3K,_15),_3M=function(_3N){var _3O=E(_3N);if(!_3O._){var _3P=jsCat(new T2(1,_3J,new T2(1,new T(function(){return String(_3O.a);}),new T2(1,_3G,new T2(1,new T(function(){return String(_3O.b);}),new T2(1,_3G,new T2(1,new T(function(){return String(_3O.c);}),_3L)))))),E(_3I));return E(_3P);}else{var _3Q=jsCat(new T2(1,_3H,new T2(1,new T(function(){return String(_3O.a);}),new T2(1,_3G,new T2(1,new T(function(){return String(_3O.b);}),new T2(1,_3G,new T2(1,new T(function(){return String(_3O.c);}),new T2(1,_3G,new T2(1,new T(function(){return String(_3O.d);}),_3L)))))))),E(_3I));return E(_3Q);}},_3R="strokeStyle",_3S="fillStyle",_3T=new T(function(){return eval("(function(e,p){return e[p].toString();})");}),_3U=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_3V=function(_3W,_3X){var _3Y=new T(function(){return B(_3M(_3W));});return function(_3Z,_){var _40=E(_3Z),_41=E(_3S),_42=E(_3T),_43=__app2(_42,_40,_41),_44=E(_3R),_45=__app2(_42,_40,_44),_46=E(_3Y),_47=E(_3U),_48=__app3(_47,_40,_41,_46),_49=__app3(_47,_40,_44,_46),_4a=B(A2(_3X,_40,_)),_4b=String(_43),_4c=__app3(_47,_40,_41,_4b),_4d=String(_45),_4e=__app3(_47,_40,_44,_4d);return new F(function(){return _3o(_);});};},_4f="lineWidth",_4g=function(_4h,_4i){var _4j=new T(function(){return String(E(_4h));});return function(_4k,_){var _4l=E(_4k),_4m=E(_4f),_4n=__app2(E(_3T),_4l,_4m),_4o=E(_3U),_4p=__app3(_4o,_4l,_4m,E(_4j)),_4q=B(A2(_4i,_4l,_)),_4r=String(_4n),_4s=__app3(_4o,_4l,_4m,_4r);return new F(function(){return _3o(_);});};},_4t=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_4u=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_4v=function(_4w,_4x,_){var _4y=E(_4w);if(!_4y._){return _37;}else{var _4z=E(_4y.a),_4A=E(_4x),_4B=__app3(E(_4t),_4A,E(_4z.a),E(_4z.b)),_4C=E(_4y.b);if(!_4C._){return _37;}else{var _4D=E(_4C.a),_4E=E(_4u),_4F=__app3(_4E,_4A,E(_4D.a),E(_4D.b)),_4G=function(_4H,_){while(1){var _4I=E(_4H);if(!_4I._){return _37;}else{var _4J=E(_4I.a),_4K=__app3(_4E,_4A,E(_4J.a),E(_4J.b));_4H=_4I.b;continue;}}};return new F(function(){return _4G(_4C.b,_);});}}},_4L=function(_4M,_4N,_4O,_4P,_4Q,_){return new F(function(){return _4v(new T2(1,new T2(0,_4M,_4N),new T2(1,new T2(0,_4O,_4N),new T2(1,new T2(0,_4O,_4P),new T2(1,new T2(0,_4M,_4P),new T2(1,new T2(0,_4M,_4N),_15))))),_4Q,_);});},_4R=function(_4S,_4T,_4U,_){var _4V=E(_4S),_4W=E(_4T);return new F(function(){return _4L(_4V.a,_4V.b,_4W.a,_4W.b,_4U,_);});},_4X=function(_4Y,_){var _4Z=E(_4Y);if(!_4Z._){return _15;}else{var _50=_4Z.b,_51=E(_4Z.a);if(!_51._){var _52=_51.b,_53=B(_4X(_50,_)),_54=new T(function(){var _55=E(_51.a);if(!_55._){return E(_3E);}else{var _56=E(_55.a),_57=function(_58,_){return new F(function(){return _4R(_56.a,_56.b,_58,_);});},_59=new T(function(){var _5a=E(E(_52).b);if(!_5a._){return E(_3E);}else{var _5b=E(_5a.a);if(!_5b._){return B(_3V(new T(function(){return B(_3f(_5b.a,_5b.b,_5b.c));},1),function(_5c,_){return new F(function(){return _3r(_57,E(_5c),_);});}));}else{return B(_3V(new T(function(){return B(_3j(_5b.a,_5b.b,_5b.c,_5b.d));},1),function(_5d,_){return new F(function(){return _3r(_57,E(_5d),_);});}));}}}),_5e=new T(function(){var _5f=E(_52),_5g=_5f.c,_5h=E(_5f.a);if(!_5h._){return E(_3E);}else{var _5i=E(_5h.a);if(!_5i._){var _5j=new T(function(){return B(_4g(_5g,function(_5k,_){return new F(function(){return _3y(_57,E(_5k),_);});}));});return B(_3V(new T(function(){return B(_3f(_5i.a,_5i.b,_5i.c));},1),_5j));}else{var _5l=new T(function(){return B(_4g(_5g,function(_5m,_){return new F(function(){return _3y(_57,E(_5m),_);});}));});return B(_3V(new T(function(){return B(_3j(_5i.a,_5i.b,_5i.c,_5i.d));},1),_5l));}}});return function(_5n,_){var _5o=B(A2(_59,_5n,_));return new F(function(){return A2(_5e,_5n,_);});};}});return new T2(1,_54,_53);}else{var _5p=B(_4X(_50,_));return new T2(1,_3E,_5p);}}},_5q=function(_5r){return E(E(_5r).a);},_5s=function(_5t){return E(E(_5t).a);},_5u=function(_5v){return E(E(_5v).b);},_5w=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_5x=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_5y=function(_){return new F(function(){return __jsNull();});},_5z=function(_5A){var _5B=B(A1(_5A,_));return E(_5B);},_5C=new T(function(){return B(_5z(_5y));}),_5D=new T(function(){return E(_5C);}),_5E=function(_5F){return E(E(_5F).b);},_5G=function(_5H){return E(E(_5H).b);},_5I=function(_5J,_5K,_5L){var _5M=B(_5q(_5J)),_5N=new T(function(){return B(_5E(_5M));}),_5O=function(_5P){var _5Q=function(_){var _5R=E(_5K);if(!_5R._){var _5S=B(A1(_5P,_37)),_5T=__createJSFunc(0,function(_){var _5U=B(A1(_5S,_));return _5D;}),_5V=__app2(E(_5x),_5R.a,_5T);return new T(function(){var _5W=Number(_5V),_5X=jsTrunc(_5W);return new T2(0,_5X,E(_5R));});}else{var _5Y=B(A1(_5P,_37)),_5Z=__createJSFunc(0,function(_){var _60=B(A1(_5Y,_));return _5D;}),_61=__app2(E(_5w),_5R.a,_5Z);return new T(function(){var _62=Number(_61),_63=jsTrunc(_62);return new T2(0,_63,E(_5R));});}};return new F(function(){return A1(_5N,_5Q);});},_64=new T(function(){return B(A2(_5G,_5J,function(_65){return E(_5L);}));});return new F(function(){return A3(_5u,B(_5s(_5M)),_64,_5O);});},_66=function(_67,_68,_69,_6a,_){var _6b=B(_4X(_69,_)),_6c=E(_67),_6d=__app1(E(_3d),_6c.b),_6e=B(_38(_6b,_6c.a,_)),_6f=B(A(_5I,[_36,_3e,function(_){var _6g=B(A1(_6a,_68));return new F(function(){return _66(_6c,_6g.a,E(_6g.b).a,_6a,_);});},_]));return _37;},_6h=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_6i=function(_6j,_6k){var _6l=function(_){var _6m=__app1(E(_6h),E(_6k)),_6n=__eq(_6m,E(_5D));return (E(_6n)==0)?new T1(1,_6m):_2N;};return new F(function(){return A2(_5E,_6j,_6l);});},_6o=new T(function(){return eval("alert");}),_6p=new T(function(){return B(unCStr("bucephalus-haste error : canvas not found."));}),_6q=function(_){var _6r=__app1(E(_6o),toJSStr(_6p));return new F(function(){return _3o(_);});},_6s=function(_6t){return E(E(_6t).f);},_6u=new T0(1),_6v=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_6w=function(_6x){return new F(function(){return err(_6v);});},_6y=new T(function(){return B(_6w(_));}),_6z=function(_6A,_6B,_6C,_6D){var _6E=E(_6D);if(!_6E._){var _6F=_6E.a,_6G=E(_6C);if(!_6G._){var _6H=_6G.a,_6I=_6G.b,_6J=_6G.c;if(_6H<=(imul(3,_6F)|0)){return new T5(0,(1+_6H|0)+_6F|0,E(_6A),_6B,E(_6G),E(_6E));}else{var _6K=E(_6G.d);if(!_6K._){var _6L=_6K.a,_6M=E(_6G.e);if(!_6M._){var _6N=_6M.a,_6O=_6M.b,_6P=_6M.c,_6Q=_6M.d;if(_6N>=(imul(2,_6L)|0)){var _6R=function(_6S){var _6T=E(_6M.e);return (_6T._==0)?new T5(0,(1+_6H|0)+_6F|0,E(_6O),_6P,E(new T5(0,(1+_6L|0)+_6S|0,E(_6I),_6J,E(_6K),E(_6Q))),E(new T5(0,(1+_6F|0)+_6T.a|0,E(_6A),_6B,E(_6T),E(_6E)))):new T5(0,(1+_6H|0)+_6F|0,E(_6O),_6P,E(new T5(0,(1+_6L|0)+_6S|0,E(_6I),_6J,E(_6K),E(_6Q))),E(new T5(0,1+_6F|0,E(_6A),_6B,E(_6u),E(_6E))));},_6U=E(_6Q);if(!_6U._){return new F(function(){return _6R(_6U.a);});}else{return new F(function(){return _6R(0);});}}else{return new T5(0,(1+_6H|0)+_6F|0,E(_6I),_6J,E(_6K),E(new T5(0,(1+_6F|0)+_6N|0,E(_6A),_6B,E(_6M),E(_6E))));}}else{return E(_6y);}}else{return E(_6y);}}}else{return new T5(0,1+_6F|0,E(_6A),_6B,E(_6u),E(_6E));}}else{var _6V=E(_6C);if(!_6V._){var _6W=_6V.a,_6X=_6V.b,_6Y=_6V.c,_6Z=_6V.e,_70=E(_6V.d);if(!_70._){var _71=_70.a,_72=E(_6Z);if(!_72._){var _73=_72.a,_74=_72.b,_75=_72.c,_76=_72.d;if(_73>=(imul(2,_71)|0)){var _77=function(_78){var _79=E(_72.e);return (_79._==0)?new T5(0,1+_6W|0,E(_74),_75,E(new T5(0,(1+_71|0)+_78|0,E(_6X),_6Y,E(_70),E(_76))),E(new T5(0,1+_79.a|0,E(_6A),_6B,E(_79),E(_6u)))):new T5(0,1+_6W|0,E(_74),_75,E(new T5(0,(1+_71|0)+_78|0,E(_6X),_6Y,E(_70),E(_76))),E(new T5(0,1,E(_6A),_6B,E(_6u),E(_6u))));},_7a=E(_76);if(!_7a._){return new F(function(){return _77(_7a.a);});}else{return new F(function(){return _77(0);});}}else{return new T5(0,1+_6W|0,E(_6X),_6Y,E(_70),E(new T5(0,1+_73|0,E(_6A),_6B,E(_72),E(_6u))));}}else{return new T5(0,3,E(_6X),_6Y,E(_70),E(new T5(0,1,E(_6A),_6B,E(_6u),E(_6u))));}}else{var _7b=E(_6Z);return (_7b._==0)?new T5(0,3,E(_7b.b),_7b.c,E(new T5(0,1,E(_6X),_6Y,E(_6u),E(_6u))),E(new T5(0,1,E(_6A),_6B,E(_6u),E(_6u)))):new T5(0,2,E(_6A),_6B,E(_6V),E(_6u));}}else{return new T5(0,1,E(_6A),_6B,E(_6u),E(_6u));}}},_7c=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_7d=function(_7e){return new F(function(){return err(_7c);});},_7f=new T(function(){return B(_7d(_));}),_7g=function(_7h,_7i,_7j,_7k){var _7l=E(_7j);if(!_7l._){var _7m=_7l.a,_7n=E(_7k);if(!_7n._){var _7o=_7n.a,_7p=_7n.b,_7q=_7n.c;if(_7o<=(imul(3,_7m)|0)){return new T5(0,(1+_7m|0)+_7o|0,E(_7h),_7i,E(_7l),E(_7n));}else{var _7r=E(_7n.d);if(!_7r._){var _7s=_7r.a,_7t=_7r.b,_7u=_7r.c,_7v=_7r.d,_7w=E(_7n.e);if(!_7w._){var _7x=_7w.a;if(_7s>=(imul(2,_7x)|0)){var _7y=function(_7z){var _7A=E(_7h),_7B=E(_7r.e);return (_7B._==0)?new T5(0,(1+_7m|0)+_7o|0,E(_7t),_7u,E(new T5(0,(1+_7m|0)+_7z|0,E(_7A),_7i,E(_7l),E(_7v))),E(new T5(0,(1+_7x|0)+_7B.a|0,E(_7p),_7q,E(_7B),E(_7w)))):new T5(0,(1+_7m|0)+_7o|0,E(_7t),_7u,E(new T5(0,(1+_7m|0)+_7z|0,E(_7A),_7i,E(_7l),E(_7v))),E(new T5(0,1+_7x|0,E(_7p),_7q,E(_6u),E(_7w))));},_7C=E(_7v);if(!_7C._){return new F(function(){return _7y(_7C.a);});}else{return new F(function(){return _7y(0);});}}else{return new T5(0,(1+_7m|0)+_7o|0,E(_7p),_7q,E(new T5(0,(1+_7m|0)+_7s|0,E(_7h),_7i,E(_7l),E(_7r))),E(_7w));}}else{return E(_7f);}}else{return E(_7f);}}}else{return new T5(0,1+_7m|0,E(_7h),_7i,E(_7l),E(_6u));}}else{var _7D=E(_7k);if(!_7D._){var _7E=_7D.a,_7F=_7D.b,_7G=_7D.c,_7H=_7D.e,_7I=E(_7D.d);if(!_7I._){var _7J=_7I.a,_7K=_7I.b,_7L=_7I.c,_7M=_7I.d,_7N=E(_7H);if(!_7N._){var _7O=_7N.a;if(_7J>=(imul(2,_7O)|0)){var _7P=function(_7Q){var _7R=E(_7h),_7S=E(_7I.e);return (_7S._==0)?new T5(0,1+_7E|0,E(_7K),_7L,E(new T5(0,1+_7Q|0,E(_7R),_7i,E(_6u),E(_7M))),E(new T5(0,(1+_7O|0)+_7S.a|0,E(_7F),_7G,E(_7S),E(_7N)))):new T5(0,1+_7E|0,E(_7K),_7L,E(new T5(0,1+_7Q|0,E(_7R),_7i,E(_6u),E(_7M))),E(new T5(0,1+_7O|0,E(_7F),_7G,E(_6u),E(_7N))));},_7T=E(_7M);if(!_7T._){return new F(function(){return _7P(_7T.a);});}else{return new F(function(){return _7P(0);});}}else{return new T5(0,1+_7E|0,E(_7F),_7G,E(new T5(0,1+_7J|0,E(_7h),_7i,E(_6u),E(_7I))),E(_7N));}}else{return new T5(0,3,E(_7K),_7L,E(new T5(0,1,E(_7h),_7i,E(_6u),E(_6u))),E(new T5(0,1,E(_7F),_7G,E(_6u),E(_6u))));}}else{var _7U=E(_7H);return (_7U._==0)?new T5(0,3,E(_7F),_7G,E(new T5(0,1,E(_7h),_7i,E(_6u),E(_6u))),E(_7U)):new T5(0,2,E(_7h),_7i,E(_6u),E(_7D));}}else{return new T5(0,1,E(_7h),_7i,E(_6u),E(_6u));}}},_7V=function(_7W){return E(E(_7W).b);},_7X=function(_7Y,_7Z,_80,_81){var _82=E(_7Z),_83=E(_81);if(!_83._){var _84=_83.b,_85=_83.c,_86=_83.d,_87=_83.e;switch(B(A3(_7V,_7Y,_82,_84))){case 0:return new F(function(){return _6z(_84,_85,B(_7X(_7Y,_82,_80,_86)),_87);});break;case 1:return new T5(0,_83.a,E(_82),_80,E(_86),E(_87));default:return new F(function(){return _7g(_84,_85,_86,B(_7X(_7Y,_82,_80,_87)));});}}else{return new T5(0,1,E(_82),_80,E(_6u),E(_6u));}},_88=function(_89,_8a,_8b,_8c){return new F(function(){return _7X(_89,_8a,_8b,_8c);});},_8d=function(_8e,_8f,_8g){var _8h=function(_8i,_8j){while(1){var _8k=E(_8j);if(!_8k._){return E(_8i);}else{var _8l=E(_8k.a),_8m=B(_88(_8e,_8l.a,_8l.b,_8i));_8i=_8m;_8j=_8k.b;continue;}}};return new F(function(){return _8h(_8f,_8g);});},_8n=function(_8o,_8p){return new T5(0,1,E(_8o),_8p,E(_6u),E(_6u));},_8q=function(_8r,_8s,_8t){var _8u=E(_8t);if(!_8u._){return new F(function(){return _7g(_8u.b,_8u.c,_8u.d,B(_8q(_8r,_8s,_8u.e)));});}else{return new F(function(){return _8n(_8r,_8s);});}},_8v=function(_8w,_8x,_8y){var _8z=E(_8y);if(!_8z._){return new F(function(){return _6z(_8z.b,_8z.c,B(_8v(_8w,_8x,_8z.d)),_8z.e);});}else{return new F(function(){return _8n(_8w,_8x);});}},_8A=function(_8B,_8C,_8D,_8E,_8F,_8G,_8H){return new F(function(){return _6z(_8E,_8F,B(_8v(_8B,_8C,_8G)),_8H);});},_8I=function(_8J,_8K,_8L,_8M,_8N,_8O,_8P,_8Q){var _8R=E(_8L);if(!_8R._){var _8S=_8R.a,_8T=_8R.b,_8U=_8R.c,_8V=_8R.d,_8W=_8R.e;if((imul(3,_8S)|0)>=_8M){if((imul(3,_8M)|0)>=_8S){return new T5(0,(_8S+_8M|0)+1|0,E(_8J),_8K,E(_8R),E(new T5(0,_8M,E(_8N),_8O,E(_8P),E(_8Q))));}else{return new F(function(){return _7g(_8T,_8U,_8V,B(_8I(_8J,_8K,_8W,_8M,_8N,_8O,_8P,_8Q)));});}}else{return new F(function(){return _6z(_8N,_8O,B(_8X(_8J,_8K,_8S,_8T,_8U,_8V,_8W,_8P)),_8Q);});}}else{return new F(function(){return _8A(_8J,_8K,_8M,_8N,_8O,_8P,_8Q);});}},_8X=function(_8Y,_8Z,_90,_91,_92,_93,_94,_95){var _96=E(_95);if(!_96._){var _97=_96.a,_98=_96.b,_99=_96.c,_9a=_96.d,_9b=_96.e;if((imul(3,_90)|0)>=_97){if((imul(3,_97)|0)>=_90){return new T5(0,(_90+_97|0)+1|0,E(_8Y),_8Z,E(new T5(0,_90,E(_91),_92,E(_93),E(_94))),E(_96));}else{return new F(function(){return _7g(_91,_92,_93,B(_8I(_8Y,_8Z,_94,_97,_98,_99,_9a,_9b)));});}}else{return new F(function(){return _6z(_98,_99,B(_8X(_8Y,_8Z,_90,_91,_92,_93,_94,_9a)),_9b);});}}else{return new F(function(){return _8q(_8Y,_8Z,new T5(0,_90,E(_91),_92,E(_93),E(_94)));});}},_9c=function(_9d,_9e,_9f,_9g){var _9h=E(_9f);if(!_9h._){var _9i=_9h.a,_9j=_9h.b,_9k=_9h.c,_9l=_9h.d,_9m=_9h.e,_9n=E(_9g);if(!_9n._){var _9o=_9n.a,_9p=_9n.b,_9q=_9n.c,_9r=_9n.d,_9s=_9n.e;if((imul(3,_9i)|0)>=_9o){if((imul(3,_9o)|0)>=_9i){return new T5(0,(_9i+_9o|0)+1|0,E(_9d),_9e,E(_9h),E(_9n));}else{return new F(function(){return _7g(_9j,_9k,_9l,B(_8I(_9d,_9e,_9m,_9o,_9p,_9q,_9r,_9s)));});}}else{return new F(function(){return _6z(_9p,_9q,B(_8X(_9d,_9e,_9i,_9j,_9k,_9l,_9m,_9r)),_9s);});}}else{return new F(function(){return _8q(_9d,_9e,_9h);});}}else{return new F(function(){return _8v(_9d,_9e,_9g);});}},_9t=function(_9u,_9v){var _9w=E(_9v);if(!_9w._){return new T0(1);}else{var _9x=E(_9w.a),_9y=_9x.a,_9z=_9x.b,_9A=E(_9w.b);if(!_9A._){return new T5(0,1,E(_9y),_9z,E(_6u),E(_6u));}else{var _9B=E(_9A.a),_9C=_9B.a;if(!B(A3(_6s,_9u,_9y,_9C))){var _9D=function(_9E,_9F,_9G,_9H){var _9I=E(_9E);if(_9I==1){var _9J=E(_9H);return (_9J._==0)?new T3(0,new T(function(){return new T5(0,1,E(_9F),_9G,E(_6u),E(_6u));}),_15,_15):(!B(A3(_6s,_9u,_9F,E(_9J.a).a)))?new T3(0,new T(function(){return new T5(0,1,E(_9F),_9G,E(_6u),E(_6u));}),_9J,_15):new T3(0,new T(function(){return new T5(0,1,E(_9F),_9G,E(_6u),E(_6u));}),_15,_9J);}else{var _9K=B(_9D(_9I>>1,_9F,_9G,_9H)),_9L=_9K.a,_9M=_9K.c,_9N=E(_9K.b);if(!_9N._){return new T3(0,_9L,_15,_9M);}else{var _9O=E(_9N.a),_9P=_9O.a,_9Q=_9O.b,_9R=E(_9N.b);if(!_9R._){return new T3(0,new T(function(){return B(_8q(_9P,_9Q,_9L));}),_15,_9M);}else{var _9S=E(_9R.a),_9T=_9S.a;if(!B(A3(_6s,_9u,_9P,_9T))){var _9U=B(_9D(_9I>>1,_9T,_9S.b,_9R.b));return new T3(0,new T(function(){return B(_9c(_9P,_9Q,_9L,_9U.a));}),_9U.b,_9U.c);}else{return new T3(0,_9L,_15,_9N);}}}}},_9V=function(_9W,_9X,_9Y){while(1){var _9Z=E(_9Y);if(!_9Z._){return E(_9X);}else{var _a0=E(_9Z.a),_a1=_a0.a,_a2=_a0.b,_a3=E(_9Z.b);if(!_a3._){return new F(function(){return _8q(_a1,_a2,_9X);});}else{var _a4=E(_a3.a),_a5=_a4.a;if(!B(A3(_6s,_9u,_a1,_a5))){var _a6=B(_9D(_9W,_a5,_a4.b,_a3.b)),_a7=_a6.a,_a8=E(_a6.c);if(!_a8._){var _a9=_9W<<1,_aa=B(_9c(_a1,_a2,_9X,_a7));_9W=_a9;_9X=_aa;_9Y=_a6.b;continue;}else{return new F(function(){return _8d(_9u,B(_9c(_a1,_a2,_9X,_a7)),_a8);});}}else{return new F(function(){return _8d(_9u,_9X,_9Z);});}}}}};return new F(function(){return (function(_ab,_ac,_ad,_ae,_af){var _ag=E(_af);if(!_ag._){return new F(function(){return _8q(_ad,_ae,_ac);});}else{var _ah=E(_ag.a),_ai=_ah.a;if(!B(A3(_6s,_9u,_ad,_ai))){var _aj=B(_9D(_ab,_ai,_ah.b,_ag.b)),_ak=_aj.a,_al=E(_aj.c);if(!_al._){return new F(function(){return _9V(_ab<<1,B(_9c(_ad,_ae,_ac,_ak)),_aj.b);});}else{return new F(function(){return _8d(_9u,B(_9c(_ad,_ae,_ac,_ak)),_al);});}}else{return new F(function(){return _8d(_9u,_ac,new T2(1,new T2(0,_ad,_ae),_ag));});}}})(1,new T5(0,1,E(_9y),_9z,E(_6u),E(_6u)),_9C,_9B.b,_9A.b);});}else{return new F(function(){return _8d(_9u,new T5(0,1,E(_9y),_9z,E(_6u),E(_6u)),_9A);});}}}},_am=function(_an,_ao){return new T2(0,new T(function(){return B(_9t(_an,_15));}),_ao);},_ap=function(_aq){return new F(function(){return toJSStr(E(_aq));});},_ar=function(_as,_at,_au,_av,_aw,_){var _ax=B(A3(_6i,_35,new T(function(){return B(_ap(_at));},1),_)),_ay=E(_ax);if(!_ay._){return new F(function(){return _6q(_);});}else{var _az=E(_ay.a),_aA=__app1(E(_B),_az);if(!_aA){return new F(function(){return _6q(_);});}else{var _aB=__app1(E(_A),_az),_aC=B(A1(_av,new T(function(){return B(_am(_as,_au));})));return new F(function(){return _66(new T2(0,_aB,_az),_aC.a,E(_aC.b).a,_aw,_);});}}},_aD=-250,_aE=new T2(0,_aD,_aD),_aF=function(_aG,_aH,_aI,_aJ,_aK){var _aL=E(_aK);if(!_aL._){var _aM=new T(function(){var _aN=B(_aF(_aL.a,_aL.b,_aL.c,_aL.d,_aL.e));return new T2(0,_aN.a,_aN.b);});return new T2(0,new T(function(){return E(E(_aM).a);}),new T(function(){return B(_6z(_aH,_aI,_aJ,E(_aM).b));}));}else{return new T2(0,new T2(0,_aH,_aI),_aJ);}},_aO=function(_aP,_aQ,_aR,_aS,_aT){var _aU=E(_aS);if(!_aU._){var _aV=new T(function(){var _aW=B(_aO(_aU.a,_aU.b,_aU.c,_aU.d,_aU.e));return new T2(0,_aW.a,_aW.b);});return new T2(0,new T(function(){return E(E(_aV).a);}),new T(function(){return B(_7g(_aQ,_aR,E(_aV).b,_aT));}));}else{return new T2(0,new T2(0,_aQ,_aR),_aT);}},_aX=function(_aY,_aZ){var _b0=E(_aY);if(!_b0._){var _b1=_b0.a,_b2=E(_aZ);if(!_b2._){var _b3=_b2.a;if(_b1<=_b3){var _b4=B(_aO(_b3,_b2.b,_b2.c,_b2.d,_b2.e)),_b5=E(_b4.a);return new F(function(){return _6z(_b5.a,_b5.b,_b0,_b4.b);});}else{var _b6=B(_aF(_b1,_b0.b,_b0.c,_b0.d,_b0.e)),_b7=E(_b6.a);return new F(function(){return _7g(_b7.a,_b7.b,_b6.b,_b2);});}}else{return E(_b0);}}else{return E(_aZ);}},_b8=function(_b9,_ba,_bb,_bc){var _bd=E(_bb),_be=E(_bc);if(!_be._){var _bf=_be.b,_bg=_be.c,_bh=_be.d,_bi=_be.e;switch(B(A3(_7V,_b9,_bd,_bf))){case 0:return new F(function(){return _7g(_bf,_bg,B(_b8(_b9,_ba,_bd,_bh)),_bi);});break;case 1:var _bj=B(A2(_ba,_bf,_bg));if(!_bj._){return new F(function(){return _aX(_bh,_bi);});}else{return new T5(0,_be.a,E(_bf),_bj.a,E(_bh),E(_bi));}break;default:return new F(function(){return _6z(_bf,_bg,_bh,B(_b8(_b9,_ba,_bd,_bi)));});}}else{return new T0(1);}},_bk=function(_bl,_bm,_bn,_bo){return new F(function(){return _b8(_bl,_bm,_bn,_bo);});},_bp=function(_bq,_br){while(1){var _bs=B((function(_bt,_bu){var _bv=new T(function(){var _bw=E(_bu),_bx=new T(function(){var _by=function(_bz,_bA){var _bB=new T(function(){var _bC=E(_bA),_bD=_bC.a,_bE=_bC.b,_bF=E(_bC.c),_bG=E(_bF.a);if(_bG>=750){return new T3(0,_bD,_bE,_aE);}else{var _bH=10-_bt|0;return new T3(0,_bD,_bE,new T2(0,_bH+_bG,new T(function(){return _bH+E(_bF.b);})));}});return new T1(1,_bB);};return B(_bk(_z,_by,_bt,_bw.a));});return new T2(0,_bx,_bw.b);}),_bI=E(_bt);if(_bI==9){return new T2(0,_37,_bv);}else{_bq=_bI+1|0;_br=_bv;return __continue;}})(_bq,_br));if(_bs!=__continue){return _bs;}}},_bJ=new T(function(){return B(unCStr("Control.Exception.Base"));}),_bK=new T(function(){return B(unCStr("base"));}),_bL=new T(function(){return B(unCStr("PatternMatchFail"));}),_bM=new T(function(){var _bN=hs_wordToWord64(new Long(18445595,3739165398,true)),_bO=hs_wordToWord64(new Long(52003073,3246954884,true));return new T5(0,_bN,_bO,new T5(0,_bN,_bO,_bK,_bJ,_bL),_15,_15);}),_bP=function(_bQ){return E(_bM);},_bR=function(_bS){var _bT=E(_bS);return new F(function(){return _1d(B(_1b(_bT.a)),_bP,_bT.b);});},_bU=function(_bV){return E(E(_bV).a);},_bW=function(_bX){return new T2(0,_bY,_bX);},_bZ=function(_c0,_c1){return new F(function(){return _1r(E(_c0).a,_c1);});},_c2=function(_c3,_c4){return new F(function(){return _2v(_bZ,_c3,_c4);});},_c5=function(_c6,_c7,_c8){return new F(function(){return _1r(E(_c7).a,_c8);});},_c9=new T3(0,_c5,_bU,_c2),_bY=new T(function(){return new T5(0,_bP,_c9,_bW,_bR,_bU);}),_ca=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_cb=function(_cc,_cd){return new F(function(){return die(new T(function(){return B(A2(_2L,_cd,_cc));}));});},_ce=function(_cf,_cg){return new F(function(){return _cb(_cf,_cg);});},_ch=function(_ci,_cj){var _ck=E(_cj);if(!_ck._){return new T2(0,_15,_15);}else{var _cl=_ck.a;if(!B(A1(_ci,_cl))){return new T2(0,_15,_ck);}else{var _cm=new T(function(){var _cn=B(_ch(_ci,_ck.b));return new T2(0,_cn.a,_cn.b);});return new T2(0,new T2(1,_cl,new T(function(){return E(E(_cm).a);})),new T(function(){return E(E(_cm).b);}));}}},_co=32,_cp=new T(function(){return B(unCStr("\n"));}),_cq=function(_cr){return (E(_cr)==124)?false:true;},_cs=function(_ct,_cu){var _cv=B(_ch(_cq,B(unCStr(_ct)))),_cw=_cv.a,_cx=function(_cy,_cz){var _cA=new T(function(){var _cB=new T(function(){return B(_1r(_cu,new T(function(){return B(_1r(_cz,_cp));},1)));});return B(unAppCStr(": ",_cB));},1);return new F(function(){return _1r(_cy,_cA);});},_cC=E(_cv.b);if(!_cC._){return new F(function(){return _cx(_cw,_15);});}else{if(E(_cC.a)==124){return new F(function(){return _cx(_cw,new T2(1,_co,_cC.b));});}else{return new F(function(){return _cx(_cw,_15);});}}},_cD=function(_cE){return new F(function(){return _ce(new T1(0,new T(function(){return B(_cs(_cE,_ca));})),_bY);});},_cF=new T(function(){return B(_cD("src/Game/Bucephalus/Object.hs:45:3-51|function move"));}),_cG=function(_cH,_cI){return E(_cH)+E(_cI);},_cJ=function(_cK,_cL){var _cM=E(_cK),_cN=E(_cL);return new T2(0,new T(function(){return B(_cG(_cM.a,_cN.a));}),new T(function(){return B(_cG(_cM.b,_cN.b));}));},_cO=function(_cP,_cQ){var _cR=E(_cQ);return new T2(0,new T(function(){return B(_cJ(_cP,_cR.a));}),new T(function(){return B(_cJ(_cP,_cR.b));}));},_cS=function(_cT,_cU){var _cV=E(_cU);return (_cV._==0)?new T1(0,new T(function(){return B(_cJ(_cT,_cV.a));})):new T1(1,new T(function(){return B(_cO(_cT,_cV.a));}));},_cW=function(_cX){var _cY=E(_cX);if(!_cY._){return __Z;}else{var _cZ=E(_cY.a),_d0=new T(function(){return B(_cW(_cY.b));}),_d1=function(_d2){var _d3=E(_d2);if(!_d3._){return E(_d0);}else{var _d4=new T(function(){var _d5=E(_d3.a);if(!_d5._){return new T2(0,new T(function(){return B(_cS(_cZ.c,_d5.a));}),_d5.b);}else{return E(_cF);}});return new T2(1,_d4,new T(function(){return B(_d1(_d3.b));}));}};return new F(function(){return _d1(_cZ.a);});}},_d6=function(_d7,_d8){while(1){var _d9=B((function(_da,_db){var _dc=E(_db);if(!_dc._){_d7=new T2(1,_dc.c,new T(function(){return B(_d6(_da,_dc.e));}));_d8=_dc.d;return __continue;}else{return E(_da);}})(_d7,_d8));if(_d9!=__continue){return _d9;}}},_dd=function(_de){return new F(function(){return _d6(_15,_de);});},_df=function(_dg){return new T2(0,new T(function(){return E(B(_bp(0,_dg)).b);}),new T1(0,new T(function(){return B(_cW(B(_dd(E(_dg).a))));})));},_dh=-260,_di=new T2(0,_dh,_dh),_dj=260,_dk=new T2(0,_dj,_dj),_dl=new T2(0,_di,_dk),_dm=new T1(1,_dl),_dn=0,_do=255,_dp=new T3(0,_dn,_dn,_do),_dq=new T1(1,_dp),_dr=3,_ds=new T3(0,_dq,_2N,_dr),_dt=new T2(0,_dm,_ds),_du=250,_dv=new T2(0,_du,_du),_dw=new T2(0,_aE,_dv),_dx=new T1(1,_dw),_dy=0.2,_dz=new T4(1,_dn,_dn,_do,_dy),_dA=new T1(1,_dz),_dB=1,_dC=new T3(0,_2N,_dA,_dB),_dD=new T2(0,_dx,_dC),_dE=new T2(1,_dD,_15),_dF=new T2(1,_dt,_dE),_dG=0,_dH=new T2(0,_dG,_dG),_dI=new T3(0,_dF,_15,_dH),_dJ=function(_dK,_dL){while(1){var _dM=B((function(_dN,_dO){var _dP=new T(function(){var _dQ=E(_dO);return new T2(0,new T(function(){return B(_88(_z,_dN,_dI,_dQ.a));}),_dQ.b);}),_dR=E(_dN);if(_dR==9){return new T2(0,_37,_dP);}else{_dK=_dR+1|0;_dL=_dP;return __continue;}})(_dK,_dL));if(_dM!=__continue){return _dM;}}},_dS=new T0(1),_dT=new T2(1,_dS,_15),_dU=new T3(0,_dT,_15,_dH),_dV=10,_dW=function(_dX){var _dY=new T(function(){var _dZ=new T(function(){var _e0=E(_dX);return new T2(0,new T(function(){return B(_88(_z,_dV,_dU,_e0.a));}),_e0.b);},1);return E(B(_dJ(0,_dZ)).b);});return new T2(0,_dY,new T1(0,new T(function(){return B(_cW(B(_dd(E(_dX).a))));})));},_e1=function(_e2){var _e3=B(_dW(_e2));return new T2(0,_e3.a,_e3.b);},_e4=new T(function(){return B(unCStr("canvas"));}),_e5=function(_){return new F(function(){return _ar(_z,_e4,_37,_e1,_df,_);});},_e6=function(_){return new F(function(){return _e5(_);});};
var hasteMain = function() {B(A(_e6, [0]));};window.onload = hasteMain;