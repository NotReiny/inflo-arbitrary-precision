class inflo {
    static isNum = /^(?<s>[+-])?(?:(?<i>\d+)(?:\.(?<f>\d*))?|\.(?<f2>\d+))(?:[Ee](?<es>[+-])?(?<e>\d+))?$/;
    static prec = 20n;
    static pow10 = 10n ** inflo.prec;
    static pow10_n = inflo.pow10 * 10n;
    static PI;
    static E;
    static LN10;
    static LN2;
    static SQRT2;
    constructor(inp) {
        const s = typeof inp === "string" ? inp : inp.toString();
        const ss = s.trim();
        const m = ss.match(inflo.isNum);
        if (!m) {
            throw new Error(`not a number: ${inp}`);
        }
        const g = m.groups;
        const sign = g.s === "-" ? -1n : 1n;
        const expSign = g.es === "-" ? -1n : 1n;
        this.e = 0n;
        // Extract fraction
        let fPart = g.f ?? g.f2 ?? "";

        // Combine integer with fraction
        let digits = (g.i ?? "0") + fPart;
        digits = digits.replace(/^0+/, ""); // Remove leading zeros
        this.man = BigInt(digits || 0);
        this.e = expSign * BigInt(g.e ?? 0) - BigInt(fPart.length);
        this.man *= sign;
        this.isz = false;
        this.__fix__();
    }

    // Improved Alignment in plus()
    plus(o) {
        let a = this.__copy__();
        let b = o instanceof inflo ? o : new inflo(o);
        if (a.isz) return b;
        if (b.isz) return a;
        // Work with copies to avoid mutating originals
        let arg1 = a;
        let arg2 = b;

        // Always make arg1 the one with the larger exponent
        if (arg2.e > arg1.e) {
            [arg1, arg2] = [arg2, arg1];
        }
        const diff = arg1.e - arg2.e;
        if (diff > inflo.prec + 2n) {
            // arg2 is so small it doesn't affect arg1 within our precision
            return arg1;
        }
        // Align arg2 to arg1's scale
        // Note: To maintain precision, we scale UP arg1 rather than scaling DOWN arg2
        arg1.man *= 10n ** diff;
        arg1.e -= diff;
        arg1.man += arg2.man;
        arg1.__fix__();
        return arg1;
    }
    minus(o) {
        // 1. Efficiently convert 'o' to an inflo instance
        let b = o instanceof inflo ? o : new inflo(o);
        // 2. A - B is the same as A + (-B)

        // This allows us to reuse the 'plus' logic entirely
        return this.plus(b.__negate__());
    }

    times(o) {
        let a = this.__copy__();
        let b = new inflo(o);

        // Directly multiply
        b.man *= a.man;
        b.e += a.e;
        b.__fix__();
        return b;
    }

    divide(o) {
        let a = this.__copy__();
        let b = new inflo(o);
        if (b.isz) throw new Error("division by zero");
        a.man *= 10n ** (inflo.prec + 1n);
        a.man /= b.man;
        a.e -= inflo.prec + 1n;
        a.e -= b.e;
        a.__fix__();
        return a;
    }

    compare(o) {
        let b = o instanceof inflo ? o : new inflo(o);
        if (this.isz && b.isz) return 0;
        if (this.man > 0n && b.man <= 0n) return 1;
        if (this.man < 0n && b.man >= 0n) return -1;

        // Compare based on exponent and mantissa
        // Note: requires both to be normalized via __fix__
        if (this.e > b.e) return this.man > 0n ? 1 : -1;
        if (this.e < b.e) return this.man > 0n ? -1 : 1;
        return this.man > b.man ? 1 : (this.man < b.man ? -1 : 0);
    }

    sqrt() {
        if (this.isz) return new inflo("0");
        if (this.man < 0n) throw new Error("not a number");
        let a = this.__copy__();
        let prevA = new inflo("-1");

        // Divide e by 2 for efficiency
        a.e = (a.e + inflo.prec) / 2n - inflo.prec;

        // Use Newton-Raphson method
        while (a.compare(prevA)) {
            prevA = a.__copy__();
            a = (new inflo(1).divide(2)).times(a.plus(this.divide(a)));
        }
        return a;
    }
    exp() {
        if (this.isz) return new inflo(1);
        // 1. Handle negative exponents: e^(-x) = 1 / e^x
        if (this.man < 0n) {
            return new inflo(1).divide(this.__negate__().exp());
        }
        // 2. Argument Reduction (Scaling and Squaring)
        // We want to scale 'x' down until it is small (e.g., < 0.5)
        let k = 0n;
        let x = this.__copy__();
        const threshold = new inflo("0.5");
        while (x.compare(threshold) > 0) {
            x = x.divide(2);
            k++;
        }
        // 3. Taylor Series for the reduced 'x'
        // e^x = 1 + x + x^2/2! + x^3/3! ...
        let term = new inflo("1");
        let sum = new inflo("1");
        let i = 1n;
        while (true) {
            // term = term * x / i
            term = term.times(x).divide(i);
            let prevSum = sum.__copy__();
            sum = sum.plus(term);
            // If the sum stops changing within our precision, we are done
            if (sum.compare(prevSum) === 0) break;
            i++;
        }
        // 4. Squaring back up: (e^(x/2^k))^(2^k)
        for (let j = 0n; j < k; j++) {
            sum = sum.times(sum);
        }
        return sum;
    }
    ln() {
        if (this.isz || this.man <= 0n) throw new Error("ln undefined for non-positive numbers");
        // 1. Argument Reduction
        // We want to transform x into x_reduced * 10^k such that 0.1 < x_reduced < 10
        // Based on your __fix__, this.man is always ~10^prec
        // x = (man / 10^prec) * 10^e
        let x = this.__copy__();
        let k = x.e + inflo.prec;
        // Normalize x to be between [0.5, 1.5] for fast convergence
        x.e = -inflo.prec;
        // 2. Further reduction if x is far from 1
        // Using ln(x) = ln(x/2) + ln(2) or similar can help, 
        // but scaling to 10^k is usually enough for 50-digit precision.
        // 3. Halley's Method or Taylor Series
        // We use the series for ln((1+z)/(1-z)) where z = (x-1)/(x+1)
        let sum = new inflo("0");
        let prevSum = new inflo("-1");
        let z = x.minus("1").divide(x.plus("1"));
        let zs = z.times(z);
        let term = z;
        let i = 1n;
        while (sum.compare(prevSum) !== 0) {
            prevSum = sum.__copy__();
            sum = sum.plus(term.divide(i));
            term = term.times(zs);
            i += 2n;
        }
        sum = sum.times("2");
        // 4. Combine: ln(x) = ln(x_reduced) + k * ln(10)
        // Note: This requires a precomputed LN10 to avoid infinite recursion
        if (k !== 0n) {
            return sum.plus(new inflo(k).times(inflo.LN10));
        }
        return sum;
    }
    log10() {
        let a = this.__copy__();
        return a.ln().divide(new inflo("10").ln());
    }
    pow(o) {
        let b = o instanceof inflo ? o : new inflo(o);
        // Handle 0^b
        if (this.isz) {
            if (b.man <= 0n) throw new Error("0^0 or 0^negative is undefined");
            return new inflo("0");
        }
        // Handle a^0
        if (b.isz) return new inflo("1");
        // Check if the exponent is an integer
        // If it is, use exponentiation by squaring (works for negative bases)
        if (b.e >= 0n || b.mod("1").isz) {
            let n = b.trunc(); // Get integer value
            return this.__intPow__(n);
        }
        // Fractional exponent logic: a^b = exp(b * ln(a))
        if (this.man < 0n) {
            throw new Error("negative base with fractional exponent");
        }
        return this.ln().times(b).exp();
    }
    floor() {
        if (this.isz) return new inflo("0");
        // 1. If the true exponent is negative, the value is between -1 and 1
        const trueExp = this.e + BigInt(this.man.toString().replace('-', '').length) - 1n;
        if (trueExp < 0n) {
            return this.man < 0n ? new inflo("-1") : new inflo("0");
        }
        // 2. Identify how many digits are fractional
        // Value = man * 10^e. If e is >= 0, it's already an integer.
        if (this.e >= 0n) return this.__copy__();
        // 3. Truncate fractional digits
        let res = this.__copy__();
        let powerOf10 = 10n ** (-this.e);
        let remainder = res.man % powerOf10;
        res.man -= remainder;
        // 4. Floor logic for negative numbers (e.g., floor(-1.1) = -2)
        if (this.man < 0n && remainder !== 0n) {
            res.man -= powerOf10;
        }
        res.__fix__();
        return res;
    }
    ceil() {
        if (this.isz) return new inflo("0");
        // If it's already an integer, return copy
        if (this.e >= 0n) return this.__copy__();
        // A simple trick for ceil: -floor(-x)
        return this.__negate__().floor().__negate__();
    }
    trunc() {
        if (this.isz) return new inflo("0");
        // Remove everything after the decimal point regardless of sign
        return this.man < 0n ? this.ceil() : this.floor();
    }
    // Optimization for mod() to help with precision:
    mod(o) {
        let b = o instanceof inflo ? o : new inflo(o);
        if (b.isz) throw new Error("division by zero");
        let aMan = this.man;
        let bMan = b.man;
        let aExp = this.e;
        let bExp = b.e;
        // Align exponents to the lower one to treat them as integers
        if (aExp > bExp) {
            aMan *= 10n ** (aExp - bExp);
            aExp = bExp;
        } else if (bExp > aExp) {
            bMan *= 10n ** (bExp - aExp);
        }
        // Use native BigInt modulo
        let resMan = aMan % bMan;
        // Create result
        let res = new inflo("0");
        res.man = resMan;
        res.e = aExp;
        res.__fix__();
        return res;
    }
    sin() {
        if (this.isz) return new inflo("0");
        // 1. Argument Reduction: x = x mod 2PI
        let x = this.mod(inflo.TAU);
        // 2. Taylor Series
        let term = x.__copy__();
        let sum = x.__copy__();
        let xSq = x.times(x);
        let i = 3n;
        while (true) {
            // term = -term * x^2 / (i * (i - 1))
            term = term.times(xSq).divide(i * (i - 1n)).__negate__();
            let prevSum = sum.__copy__();
            sum = sum.plus(term);
            if (sum.compare(prevSum) === 0) break;
            i += 2n;
        }
        return sum;
    }
    cos() {
        if (this.isz) return new inflo("1");
        return this.minus(inflo.PI.divide(2)).sin().__negate__();
    }
    tan() {
        let s = this.sin();
        let c = this.cos();
        if (c.isz) throw new Error("tangent undefined (division by zero)");
        return s.divide(c);
    }
    toString() {
        if (this.isz) return "0";
        // 1. Get the absolute mantissa and the sign
        let s = (this.man < 0n ? -this.man : this.man).toString();
        const sign = this.man < 0n ? "-" : "";
        // 2. Calculate the 'true' exponent 
        // Since __fix__ ensures s.length is always prec + 1 (e.g., 25 digits),
        // the value is (mantissa / 10^prec) * 10^e
        // True Exponent = e + (s.length - 1)
        const trueExp = this.e + BigInt(s.length) - 1n;
        // 3. Remove trailing zeros for a cleaner look
        s = s.replace(/0+$/, "");
        // 4. Determine format: Fixed vs Scientific
        // Use Fixed if exponent is reasonably small (e.g., between -6 and 15)
        if (trueExp > -7n && trueExp < 21n) {
            if (trueExp >= 0n) {
                // Number >= 1 (e.g., 123.45)
                const intPart = s.slice(0, Number(trueExp) + 1).padEnd(Number(trueExp) + 1, "0");
                const fracPart = s.slice(Number(trueExp) + 1);
                return `${sign}${intPart}${fracPart ? "." + fracPart : ""}`;
            } else {
                // Number < 1 (e.g., 0.00123)
                const leadingZeros = "0".repeat(Math.abs(Number(trueExp)) - 1);
                return `${sign}0.${leadingZeros}${s}`;
            }
        }
        // 5. Fallback: Scientific Notation (e.g., 1.23e+10)
        const firstDigit = s[0];
        const rest = s.slice(1);
        const expSign = trueExp >= 0 ? "" : ""; // optional: standard plus sign
        return `${sign}${firstDigit}${rest ? "." + rest : ""}e${expSign}${trueExp}`;
    }
    __copy__() {
        const x = Object.create(inflo.prototype);
        x.man = this.man;
        x.e = this.e;
        x.isz = this.isz;
        return x;
    }
    // Add this helper to the class to flip signs without re-parsing strings
    __negate__() {
        const x = this.__copy__();
        x.man = -x.man;
        // isz (is zero) doesn't change when negating
        return x;
    }
    // Helper: Exponentiation by Squaring
    __intPow__(n) {
        let x = this.__copy__();
        if (n.compare("0") === -1) {
            return new inflo("1").divide(x.__intPow__(n.__negate__()));
        }
        let res = new inflo("1");
        while (n.compare("0") === 1) {
            if (n.mod("2").compare("1") === 0) res = res.times(x);
            x = x.times(x);
            n = n.divide("2").trunc();
        }
        return res;
    }
    __fix__() {
        if (this.man === 0n) {
            this.e = 0n;
            this.isz = true;
            return;
        }
        this.isz = false;
        let absoluteMan = this.man < 0n ? -this.man : this.man;
        let s = absoluteMan.toString();
        let targetLen = Number(inflo.prec) + 1;
        let diff = s.length - targetLen;
        if (diff > 0) {
            const divisor = 10n ** BigInt(diff);
            const half = divisor / 2n;
            const remainder = absoluteMan % divisor;
            // Perform the truncation
            absoluteMan /= divisor;
            // If the remainder is >= 0.5 of the divisor, round up
            if (remainder >= half) {
                absoluteMan += 1n;
            }
            // Restore the sign and update exponent
            this.man = this.man < 0n ? -absoluteMan : absoluteMan;
            this.e += BigInt(diff);
            // Re-check: rounding up 999... could increase digit length
            if (absoluteMan.toString().length > targetLen) {
                this.man /= 10n;
                this.e += 1n;
            }
        } else if (diff < 0) {
            this.man *= 10n ** BigInt(-diff);
            this.e -= BigInt(-diff);
        }
    }
    static recompute() {
        // Helper for ln(x) using Taylor series for 2 * artanh((x-1)/(x+1))
        // This avoids using the static LN10 property during initial boot
        const internalLn = (strVal) => {
            let x = new inflo(strVal);
            let sum = new inflo("0");
            let prevSum = new inflo("-1");
            let z = x.minus("1").divide(x.plus("1"));
            let zs = z.times(z);
            let term = z;
            let i = 1n;
            while (sum.compare(prevSum) !== 0) {
                prevSum = sum.__copy__();
                sum = sum.plus(term.divide(i));
                term = term.times(zs);
                i += 2n;
            }
            return sum.times("2");
        };
        // 1. Calculate PI using Machin-like formula
        const atan = (x_inv) => {
            let xInvInflo = new inflo(x_inv);
            let xSq = xInvInflo.times(xInvInflo);
            let sum = new inflo("0"),
                term = new inflo("1").divide(xInvInflo),
                i = 1n;
            while (true) {
                let prev = sum.__copy__();
                let step = term.divide(i);
                sum = (i % 4n === 1n) ? sum.plus(step) : sum.minus(step);
                if (sum.compare(prev) === 0) break;
                term = term.divide(xSq);
                i += 2n;
            }
            return sum;
        };
        inflo.PI = atan("5").times("4").minus(atan("239")).times("4");
        // 2. Fundamental Logarithms
        inflo.LN2 = internalLn("2");
        const ln5 = internalLn("5");
        inflo.LN10 = inflo.LN2.plus(ln5);
        // 3. Calculate E via exp(1) - now safe because LN10 is set
        inflo.E = new inflo("1").exp();
        // 4. Common Roots
        inflo.SQRT2 = new inflo("2").sqrt();
    }
    // Getters for derivative constants (Computes only when asked)
    static get TAU() {
        return inflo.PI.times("2");
    }
    static get GOLDEN_RATIO() {
        return new inflo("5").sqrt().plus("1").divide("2");
    }
}
inflo.recompute(); // Initialize constants