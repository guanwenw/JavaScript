var yourself = {
    fibonacci : function(n) {
        var zero = 0;
        var one = 1;
        for(var i = 0; i <= n - 2; i += 2) {
            zero = zero + one;
            one = one + zero;
        }
        if (n % 2)
            return one;
        return zero;
    }
};
