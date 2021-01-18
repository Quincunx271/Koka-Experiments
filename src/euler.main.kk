import std/os/env
import std/num/ddouble
import std/num/int32

val problems: list<() -> <div,exn> string> = [ignore, problem1, problem2, problem3, problem4]

fun main() {
    val n = get-argv()[1].unjust
        .parse-int
        .unjust
    problems[n].unjust()().println
}

fun ignore() {
    "Not a problem"
}

fun problem1() {
    list(1, 1000 - 1)
        .filter fn(x) { x % 5 == 0 || x % 3 == 0 }
        .sum
        .show
}

co type lazy-stream<a> {
    Empty
    Yield(head: a, tail: () -> div lazy-stream<a>)
}

fun map(xs: lazy-stream<a>, f: (a) -> b): div lazy-stream<b> {
    match xs {
        Empty -> Empty
        Yield(head, tail) -> Yield(f(head)) { map(tail(), f) }
    }
}

fun filter(xs: lazy-stream<a>, p: (a) -> bool): div lazy-stream<a> {
    match xs {
        Empty -> Empty
        Yield(head, tail) ->
            if (p(head)) Yield(head) { filter(tail(), p) }
            else filter(tail(), p)
    }
}

fun take'(xs: lazy-stream<a>, n: int): div list<a> {
    if (n == 0) return Nil
    match xs {
        Empty -> Nil
        Yield(head, tail) -> Cons(head, take'(tail(), n - 1))
    }
}

fun take(xs: lazy-stream<a>, n: int): list<a> {
    unsafe-nodiv { take'(xs, n) }
}

fun takewhile(xs: lazy-stream<a>, p: (a) -> bool): div list<a> {
    match xs {
        Empty -> Nil
        Yield(head, tail) ->
            if (!p(head)) Nil
            else Cons(head, takewhile(tail(), p))
    }
}

fun foldl(xs: lazy-stream<a>, init: b, f: (b, a) -> b): <div> b {
    match xs {
        Empty -> init
        Yield(head, tail) -> foldl(tail(), f(init, head), f)
    }
}

fun maximum(xs: lazy-stream<int>): div maybe<int> {
    foldl(xs, Nothing) fn (acc, i) {
        match acc {
            Nothing -> Just(i)
            Just(cur) -> Just(max(cur, i))
        }
    }
}

fun fib(last = 1, cur = 1): div lazy-stream<int> {
    Yield(cur) { fib(cur, last + cur) }
}

fun problem2() {
    fib()
        .filter(fn (x) { x % 2 == 0 })
        .takewhile(fn (x) { x < 4000000 })
        .sum
        .show
}

fun primes-limited(limit: int): list<int> {
    if (limit < 2) return []
    if (limit == 2) return [2]
    if (limit < 5) return [2, 3]

    with unsafe-noexn
    with unsafe-nodiv

    fun to-index(x: int): int {
        (x - 1) / 2 - 1
    }
    fun from-index(i: int): int {
        i * 2 + 3
    }

    var sieve := vector(to-index(limit) + 1, default = True)

    foreach-indexed(sieve) fn (isprime, index) {
        if (isprime) {
            val n = from-index(index)
            val cur = ref(3 * n)

            while {!cur <= limit} {
                sieve[to-index(!cur)] := False
                cur := !cur + 2 * n
            }
        }
    }

    var primes: list<int> := [2]

    foreach-indexed(sieve) fn (isprime, index) {
        if (isprime) primes := Cons(from-index(index), primes)
    }

    primes.reverse
}

fun prime-factors(n: int, primes: list<int>): list<int> {
    var factors := []

    foreach-while (primes) fn (p) {
        if (p * p >= n) return Just(());
        if (n % p == 0) factors := Cons(p, factors)
        return Nothing;
    }

    factors.reverse
}

fun prime-factors-multi(n: int, primes: list<int>): list<int> {
    var factors := []

    val n' = ref(n)
    foreach-while (primes) fn (p) {
        if (p > !n') return Just(())

        with unsafe-nodiv
        while {!n' % p == 0} {
            factors := Cons(p, factors)
            n' := !n' / p
        }

        return Nothing
    }

    factors.reverse
}

fun problem3() {
    val num = 600851475143

    val sqrtnum = num.ddouble
        .sqrt
        .round
        .int

    val primes = primes-limited(sqrtnum)

    prime-factors(num, primes)
        .maximum
        .show
}

fun digits10(x: int): int32 {
    var num := x
    var count: int32 := 0.int32

    with unsafe-nodiv

    while {num > 0} {
        num := num / 10
        count := count + 1.int32
    }

    count
}

fun split-digits10(x: int): list<int32> {
    var num := x
    var result := []

    with unsafe-nodiv

    while {num > 0} {
        result := Cons(int32(num % 10), result)
        num := num / 10
    }

    result
}

fun join-digits10(x: list<int32>): int {
    var num := 0

    foreach(x.reverse) fn (d) {
        num := num * 10 + d.int
    }

    num
}

fun palindromes-down-from(xs: list<int32>): lazy-stream<int> {
    if (xs.is-nil) return Empty

    fun palindromes-impl<h>(x: ref<h, vector<int32>>): <div,read<h>> lazy-stream<int> {
        if ((!x).list.all fn (d) { d == 0.int32 }) return Empty

        with unsafe-noexn

        fun reflect(i) {
            (!x).length - i - 1
        }

        for-while((!x).length / 2, (!x).length - 1) fn (i) {
            val digit = (!x)[i]
            var x' := !x

            if (digit > 0.int32) {
                x'[i] := digit - 1.int32
                x'[reflect(i)] := digit - 1.int32
                Just(())
            } else {
                x'[i] := 9.int32
                x'[reflect(i)] := 9.int32
                Nothing
            }
        }

        Yield(join-digits10((!x).list)) {
            with unsafe-total
            palindromes-impl(x)
        }
    }

    with unsafe-nodiv
    return palindromes-impl(ref(xs.vector))
}

fun (==)(lhs: list<int>, rhs: list<int>): bool {
    if (lhs.length != rhs.length) return False
    lhs.zip(rhs).foldl(True) fn (acc: bool, x: (int, int)) { acc && x.fst == x.snd }
}

fun (==)(lhs: list<int32>, rhs: list<int32>): bool {
    if (lhs.length != rhs.length) return False
    !lhs.zip(rhs).foreach-while fn (arg) {
        val (x, y) = arg
        if (x != y) Just(False)
        else Nothing
    }.bool
}

fun is-palindromic(x: int): bool {
    val digits = split-digits10(x)
    digits == digits.reverse
}

fun problem4() {
    val candidates: lazy-stream<int> = palindromes-down-from(999999.split-digits10)

    var max := 0

    list(111, 999).reverse.foreach-while fn (x) {
        list(x, 999).reverse.foreach-while fn(y) {
            if (x * y < max) return Just(())

            if (is-palindromic(x * y)) {
                max := x * y
            }
            Nothing
        }
        if (x * 999 < max) Just(())
        else Nothing
    }
    max.show

    // val primes = primes-limited(999999)
    // candidates
    //     .filter fn (i) { i <= max3prod }
    //     .filter fn (i) { i.prime-factors-multi(primes).length >= 15 }
    //     .map(show)
    //     // .map fn (i) { i.prime-factors-multi(primes) }
    //     // .filter fn (ps) { ps.all fn (p) { p.digits10 <= 3.int32 } }
    //     .take(100)
    //     .join("\n")
}
