nq = list(input().split())
n = int(nq[0])
q = int(nq[1])

nums = list(map(int, input().split()))

# Authors: Morteza Farrokhnejad, Ali Farrokhnejad
i = 0
search = []
for i in range(q):
    search.append(int(input()))

for i in range(q):
    num = search[i]
    
    left = 0
    right = n - 1
    start = -1
    
    
    while left <= right:
        mid = (left + right) // 2
        if nums[mid] == num:
            start = mid
            right = mid - 1
        elif nums[mid] < num:
            left = mid + 1
        else:
            right = mid -1
    if start == -1:
        print ("-1 -1")
        continue
    
    left = 0
    right = n - 1
    end = -1
    
    while left <= right:
        mid = (left + right) // 2
        if nums[mid] == num:
            end = mid
            left = mid + 1
        elif nums[mid] < num:
            left = mid + 1
        else:
            right = mid - 1
    
    print (f"{start+1} {end+1}")