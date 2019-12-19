function O = alpha(o,i1,i2,i3,i4)
% ALPHA Implements the composition of four functions alpha_i(o) =
% -e_i*(o*e_i), where i are indices given as ALPHA function arguments. 
% 
% This implementation uses the fact -ALPHA(o,i1,i2,i3,i4) changes the sign
% of four (different) imaginary units of an octonion o.

narginchk(5, 5), nargoutchk(0, 1)

if ~isreal(o)
    error('The first argument must be a real octonion.');
end

in = [i1, i2, i3, i4];
if numel(in)~=numel(unique(in))
    error('Indices i1, i2, i3 and i4 are not unique.');
end

if ~all(mod(in,1) == 0) || ~all(in >= 1) || ~all(in <= 7)
    error('Indices i1, i2, i3 and i4 must be values from set {1,...,7}.');
end

o0 = part(o,1); o4 = part(o,5);
o1 = part(o,2); o5 = part(o,6);
o2 = part(o,3); o6 = part(o,7);
o3 = part(o,4); o7 = part(o,8);

for i = in
    switch i
        case 1, o1 = -o1;
        case 2, o2 = -o2;
        case 3, o3 = -o3;
        case 4, o4 = -o4;
        case 5, o5 = -o5;
        case 6, o6 = -o6;
        case 7, o7 = -o7;
    end
end

O = octonion(-o0,-o1,-o2,-o3,-o4,-o5,-o6,-o7);