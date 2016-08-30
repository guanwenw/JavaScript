// Compiler Design
// @author Guanwen Wang
// Finished

var startSymbol = null;
var nonTerminals = [];
var allSymbols = [];
var terminals = [];
var nullDerivings = [];
var firstSets = [];
var followSets = [];
var predictSets = [];
var proList = [];
var flag = true;

var indexOf = function(arr, value){
    var i;
    i = 0;
    var size;
    size = arr.getSize();
    var tmp;
    while(i < size){
        tmp = arr.getVal(i);
        if(tmp == value)
            return i;
        i = i + 1;
    } 
    return -1;
};

var reportStartSymbol = function(){
    print startSymbol + "\n";
};

var report = function( arr ){
    var i;
    i = 0;
    var size;
    size = arr.getSize();
    var result;
    result = "";
    while(i < size){
        result = result + arr.getVal(i) + " ";
        i = i + 1;
    }
    print result + "\n";
};

var reportSets = function(set){
    size = set.getSize();
    i = 0;
    while(i < size){
        j = 0;
        result = "";
        tmp = set.getVal(i);
        sizeLine = tmp.getSize();
        while(j < sizeLine){
            if(j == 0)
                result = tmp.getVal(j) + ": ";
            else
                result = result + tmp.getVal(j) + " ";
            j = j + 1;
        }
        i = i + 1;
        print result;
    }
    //print "\n";
};

var loadAndParse = function(){

    var i;
    var size;
    var tmpInput;
    var first;
    var input;
    input = readln();
    while(input){
        //print(input);
        tmpInput = parse(input);
        //add into production List
        proList.pushIn(tmpInput);
        if(startSymbol == null){
            startSymbol = tmpInput.getVal(0);
        }
        first = tmpInput.getVal(0);

        nonTerminals.addIn(first); 
        size = tmpInput.getSize();
        i = 0;
        while( i < size ){
            allSymbols.addIn(tmpInput.getVal(i));
            i = i + 1;
        }
        if(size == 1)
            nullDerivings.addIn(first);

        input = readln();
    }
};

var findTerminals = function(){
    var sym;
    var i;
    i = 0;
    var size;
    size = allSymbols.getSize();
    while(i < size){
        sym = allSymbols.getVal(i);
        if(!nonTerminals.contains(sym))
            terminals.addIn(sym);
        i = i + 1;
    }
};

var findNullDerivings = function(){
    var i;
    var size;
    size = proList.getSize();
    var unitSize;
    var proLine;
    var j;
    var delList;
    delList= [];
    var term;

    var noUpdate;
    noUpdate = 0;

    while(!(noUpdate == size)){ 
        noUpdate = 0;
        i = 0;
        while(i < size){
            proLine = proList.getVal(i);
            unitSize = proLine.getSize();
            j = unitSize - 1;
            while(j > 0){
                term = proLine.getVal(j);
                if( ! nullDerivings.contains(term)){
                    break;
                } 
                j = j - 1; 
            }

            if(j == 0){
                if(! nullDerivings.contains(proLine.getVal(0))){
                    nullDerivings.addIn(proLine.getVal(0));
                }
                else{
                    noUpdate = noUpdate + 1;
                }
            }
            else{
                noUpdate = noUpdate + 1;
            }
            i = i + 1; 
        }
    }
};

var initSet = function(set){
    var i;
    i = 0;
    var size;
    size = nonTerminals.getSize();
    var tmp;
    while(i < size){
        var firstLine;
        firstLine = [];
        tmp = nonTerminals.getVal(i);
        firstLine.addIn(tmp);
        set.addIn(firstLine);
        i = i + 1;
    }
};

var copySets = function(update, fromSet, from, toSet, to){

    indFrom = indexOf(nonTerminals, from);
    ptFrom = fromSet.getVal(indFrom);

    indTo = indexOf(nonTerminals, to);
    ptTo = toSet.getVal(indTo);

    localSize = ptFrom.getSize();
    ii = 1;
    while(ii < localSize){
        localVar = ptFrom.getVal(ii);
        if(!ptTo.contains(localVar)){
            ptTo.addIn(localVar);
            update = true;
            flag = true;
        }
        ii = ii + 1;
    }
    return update;  
};

var findFirst = function(){
    size = proList.getSize();
    update = true;
    while(update){
        update = false;
        i = 0;
        while(i < size){

            tmp = proList.getVal(i);
            sizeLine = tmp.getSize();
            if(sizeLine > 1){
                j = 1;

                lhs = tmp.getVal(0);
                while(j < sizeLine){

                    rhs = tmp.getVal(j);
                    if(terminals.contains(rhs)){
                        ind = indexOf(nonTerminals, lhs);
                        ptFirst = firstSets.getVal(ind);
                        if(!ptFirst.contains(rhs)){
                            ptFirst.addIn(rhs);
                            update = true;
                            flag = true;
                        }
                        break;
                    }
                    else if(nonTerminals.contains(rhs)){
                        update = copySets(update, firstSets, rhs, firstSets, lhs);

                        if(!nullDerivings.contains(rhs))
                            break;
                    }
                    j = j + 1;
                }
            }
            i = i + 1;
        }
    }
};

var findFollowSet = function(){
    folToken = followSets.getVal(0);
    folToken.addIn("EOF");

    size = proList.getSize();
    update = true;
    while(update){
        update = false;
        i = 0;
        while(i < size){
            proLine = proList.getVal(i);
            sizeLine = proLine.getSize();
            j = sizeLine - 1;
            lhs = proLine.getVal(0);
            while(j > 0){
                rhs = proLine.getVal(j);
                if(terminals.contains(rhs)){
                    break;
                }
                else{
                    update = copySets(update, followSets, lhs, followSets, rhs);
                    if(!nullDerivings.contains(rhs))
                        break;
                }
                j = j - 1;
            }
            i = i + 1;
        }
    }
};

var findFollowPro= function(){
    size = proList.getSize();
    update = true;
    while(update){
        update = false;
        i = 0;
        while(i < size){
            proLine = proList.getVal(i);
            sizeLine = proLine.getSize();

            j = sizeLine - 2;
            while(j > 0){
                rhs = proLine.getVal(j);
                if(nonTerminals.contains(rhs)){
                    indRHS = indexOf(nonTerminals, rhs);
                    ptFollow = followSets.getVal(indRHS);
                    k = j + 1;
                    while(k < sizeLine){
                        subRHS = proLine.getVal(k);
                        if(terminals.contains(subRHS)){
                            if(!ptFollow.contains(subRHS)){
                                ptFollow.addIn(subRHS);
                                update = true;
                                flag = true;
                            }
                            break;
                        }
                        else{
                            update = copySets(update, firstSets, subRHS, followSets, rhs);
                            if(!nullDerivings.contains(subRHS))
                                break;
                        }
                        k = k + 1;
                    }
                }
                j = j - 1;
            }
            i = i + 1;
        }
    }
};

var findFollow = function(){
    flag = true;
    while(flag){
        flag = false;
        findFollowSet();
        findFollowPro();
    }
};

var initPredictSets = function(){
    var i;
    i = 0;
    var size;
    size = proList.getSize();
    var tmp;
    while(i < size){
        var firstLine;
        firstLine = [];
        predictSets.addIn(firstLine);
        i = i + 1;
    }
};

var copySetsII = function(fromSet, from, toSet, indTo){

    indFrom = indexOf(nonTerminals, from);
    ptFrom = fromSet.getVal(indFrom);

    ptTo = toSet.getVal(indTo);

    localSize = ptFrom.getSize();
    ii = 1;
    while(ii < localSize){
        localVar = ptFrom.getVal(ii);
        if(!ptTo.contains(localVar)){
            ptTo.addIn(localVar);
        }
        ii = ii + 1;
    }
};

var findPredictSet = function(){
    size = proList.getSize();
    i = 0;
    while(i < size){

        proLine = proList.getVal(i);
        sizeLine = proLine.getSize();
        lhs = proLine.getVal(0);
        if(sizeLine == 1){
            copySetsII(followSets, lhs, predictSets, i); 
        }

        j = 1;
        while(j < sizeLine){
            rhs = proLine.getVal(j);
            if(terminals.contains(rhs)){
                ptPredict = predictSets.getVal(i);
                ptPredict.addIn(rhs);
                break;
            }
            else{
                copySetsII(firstSets, rhs, predictSets, i);               

                if(!nullDerivings.contains(rhs))
                    break;
            }
            //TODO: look like need to check if j = sizeLine -1
            //then add lhs follow Sets
            if(j == (sizeLine - 1)){
                copySetsII(followSets, lhs, predictSets, i);
            }
            j = j + 1;
        }    
        i = i + 1;
    }
};

var reportPredictSets = function(){
    size = proList.getSize();
    i = 0;
    while(i < size){

        j = 0;
        result = "";
        tmp = proList.getVal(i);
        sizeLine = tmp.getSize();
        while(j < sizeLine){
            result = result + tmp.getVal(j) + " ";
            j = j + 1;
        }
        print result;

        j = 0;
        result = "";
        tmp = predictSets.getVal(i);
        sizeLine = tmp.getSize();
        while(j < sizeLine){
            result = result + tmp.getVal(j) + " ";
            j = j + 1;
        }
        print result + "\n";

        i = i + 1;
    }
};

var isLLOne = function(){
    var allPool;
    var totalSize;
    i = 0;
    size = nonTerminals.getSize();

    while(i < size){
        term = nonTerminals.getVal(i);

        j = 0;
        sizePro = proList.getSize();
        allPool = [];
        totalSize = 0;

        while(j < sizePro){
            proLine = proList.getVal(j);
            lhs = proLine.getVal(0);

            if(lhs == term){
                k = 0;
                ptPre = predictSets.getVal(j);
                sizePre = ptPre.getSize();
                totalSize = totalSize + ptPre.getSize();

                while(k < sizePre){
                    token = ptPre.getVal(k);
                    allPool.addIn(token);
                    k = k + 1;
                }

                poolSize = allPool.getSize();
                if(!(totalSize == poolSize))
                    return false;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return true;
};

var main = function() {
    loadAndParse();

    print "Start Symbol\n";
    reportStartSymbol();

    print "Nonterminals\n";
    report(nonTerminals);

    print "Terminals\n";
    findTerminals();
    report(terminals);

    print "Null-Deriving Nonterminals\n"; 
    findNullDerivings(); 
    report(nullDerivings);

    print "First Sets\n";
    initSet(firstSets);
    findFirst();
    reportSets(firstSets);

    print "\nFollow Sets\n";
    initSet(followSets);
    findFollow();
    reportSets(followSets);

    print "\nPredict Sets\n";
    initPredictSets();
    findPredictSet();
    reportPredictSets();

    isLL = isLLOne();
    if(isLL)
        print "The grammar is LL(1).\n";
    else
        print "The grammar is NOT LL(1).\n";
};

main();
