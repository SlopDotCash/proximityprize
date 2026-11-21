"""Check the four-head first-field ceiling ceil(7n/24) using exact arithmetic."""
from probe_rate_half_eight_fibers import G, N, P, check_explicit_witnesses, require


PARTITIONS = (
    ('123', '0'), ('123', '0'), ('023', '1'), ('13', '0', '2'),
    ('013', '2'), ('023', '1'), ('012', '3'), ('0', '1', '2', '3'),
    ('123', '0'), ('013', '2'), ('023', '1'), ('02', '1', '3'),
    ('013', '2'), ('012', '3'), ('012', '3'), ('03', '12'),
)


def quotient_values():
    omega = pow(G, N // 16, P)
    require(pow(omega, 8, P) == P - 1, 'order sixteen')
    values = []
    for i in range(4):
        a = pow(omega, 4*i, P)
        row = []
        for j in range(16):
            y = pow(omega, j, P)
            locator = y**6 + a*y**4 + a**2*y**2 + a**3
            linear = (a + omega**2*a**2)*y + omega**5 + omega**3*a**3
            row.append(locator*linear % P)
        values.append(row)
    for j, groups in enumerate(PARTITIONS):
        observed = {}
        for i, row in enumerate(values):
            observed[row[j]] = observed.get(row[j], '') + str(i)
        require(set(observed.values()) == set(groups), 'seven-degree head partition')
    return values


def allocation(n):
    s, rem = divmod(n, 16)
    t, mod = divmod(s, 6)
    require(rem == 0 and mod == 4 and t >= 1, 's = 6t+4 with t positive')
    rows = [[(groups[0], s)] for groups in PARTITIONS]
    rows[7] = [('root', 4*t+3), ('off', 2*t+1)]
    rows[3] = [('root', t-1), ('13', s-t+1)]
    rows[11] = [('root', t), ('02', s-t)]
    rows[15] = [('03', s//2), ('12', s//2)]
    cores = [0]*4
    roots = labels = 0
    for j, slots in enumerate(rows):
        require(sum(count for _, count in slots) == s, 'full fiber')
        for action, count in slots:
            if action == 'root':
                roots += count
                group = '0123'
            elif action == 'off':
                labels += len(PARTITIONS[j])*count
                group = ''
            else:
                require(action in PARTITIONS[j], 'normal allocation')
                labels += count
                group = action
            for i in group:
                cores[int(i)] += count
    errors = n - min(cores) - 1
    require(roots == s-2 and 7*s+roots+1 < n//2, 'polynomial degree')
    require(min(cores) == 68*t+44 and min(cores) >= n//2, 'agreement cores')
    require(labels == n+1 and errors == (7*n+23)//24, 'label and error counts')

    def slot(j, within):
        for action, count in rows[j]:
            if within < count:
                return action if action in ('root', 'off') else tuple(map(int, action))
            within -= count
        raise AssertionError('fiber index')

    return slot, cores, errors, labels


def main():
    values = quotient_values()
    _, cores, errors, labels = allocation(N)
    require(P//2**128 == N and 4*(N+1)+1 < P, 'production field and security budget')
    require(errors == 313174699 and labels == 1073741825, 'production endpoint')
    print(f'production n={N} errors={errors} joint_cores={cores} bad_labels={labels}')
    for n in (256, 1024):
        slot, cores, errors, labels = allocation(n)
        check_explicit_witnesses(n, values, slot, cores, errors, labels)


if __name__ == '__main__':
    main()
