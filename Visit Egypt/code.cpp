#include <bits/stdc++.h>
using namespace std;

const int MOD = 1000000007;

// Author: Morteza Farrokhnejad, Ali Farrokhnejad
// Denominations in units of 25 to simplify processing
const int denominations[] = {1, 2, 4, 20, 40, 80, 200, 400, 800};
const int DENOM_COUNT = 9;

// Limits
const int MAX_EUROS = 100000;
const int MAX_AMOUNT = 212 * MAX_EUROS;

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    
    static int ways[MAX_AMOUNT + 1];
    ways[0] = 1;

    for (int amount = 1; amount <= MAX_AMOUNT; ++amount) {
        long long countSum = 0;
        for (int i = 0; i < DENOM_COUNT; ++i) {
            int coinValue = denominations[i];
            if (amount >= coinValue) {
                countSum += ways[amount - coinValue];
                if (countSum >= (1ll << 62)) countSum %= MOD; 
            }
        }
        ways[amount] = static_cast<int>(countSum % MOD);
    }

    int testCases;
    if (!(cin >> testCases)) return 0;

    while (testCases--) {
        long long eurosInput, mikelGuess, andrewGuess;
        cin >> eurosInput >> mikelGuess >> andrewGuess;

        int euros = static_cast<int>(eurosInput);
        int totalReduced = 212 * euros;
        int actualCombinations = ways[totalReduced];

        long long mikelValue = (mikelGuess % MOD + MOD) % MOD;
        long long andrewValue = (andrewGuess % MOD + MOD) % MOD;

        if (mikelValue == actualCombinations && andrewValue == actualCombinations) {
            cout << "TIE\n";
            continue;
        }

        long long diffMikel = llabs(mikelValue - (long long)actualCombinations);
        long long diffAndrew = llabs(andrewValue - (long long)actualCombinations);

        if (diffMikel < diffAndrew)
            cout << "Mikel\n";
        else if (diffAndrew < diffMikel)
            cout << "Andrew\n";
        else
            cout << "NONE\n";
    }

    return 0;
}
