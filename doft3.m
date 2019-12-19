function Y = doft3(X)
% DOFT3 Discrete octonion Fourier transform calculated with direct formula
% 
% This function calculates the discrete octonion Fourier transform of
% 3-dimensional octonion-valued matrix X using direct formula. It uses the 
% convention that zero frequencies appear on the first coordinates of the 
% matrix. In order to shift the zero frequency to the middle of the matrix, 
% the fftshift function should be used.
% 
% See also: IDOFT3, FFTSHIFT

narginchk(1, 1), nargoutchk(0, 1)

if ~isreal(X)
    error(['The transformed matrix must have components that are ', ...
        'real octonions.']);
end

if ndims(X) ~= 3
    error('The transformed matrix must be 3-dimensional.');
end

[N1, N2, N3] = size(X);

Y = octonion(zeros(N1,N2,N3));

for k1 = 0:N1-1, for k2 = 0:N2-1, for k3 = 0:N3-1
    y = zeros(8,1);
    for n1 = 0:N1-1, for n2 = 0:N2-1, for n3 = 0:N3-1
        for i = 1:8, x(i,1) = part(X(n1+1,n2+1,n3+1),i); end
        e1c = cos(2*pi*k1*n1/N1); e1s = -sin(2*pi*k1*n1/N1);
        e2c = cos(2*pi*k2*n2/N2); e2s = -sin(2*pi*k2*n2/N2);
        e4c = cos(2*pi*k3*n3/N3); e4s = -sin(2*pi*k3*n3/N3);
        E1 = diag(e1c*ones(8,1));
        E1(1,2) = -e1s; E1(2,1) =  e1s; E1(3,4) =  e1s; E1(4,3) = -e1s;
        E1(5,6) =  e1s; E1(6,5) = -e1s; E1(7,8) = -e1s; E1(8,7) =  e1s;
        E2 = diag(e2c*ones(8,1));
        E2(1,3) = -e2s; E2(2,4) = -e2s; E2(3,1) =  e2s; E2(4,2) =  e2s;
        E2(5,7) =  e2s; E2(6,8) =  e2s; E2(7,5) = -e2s; E2(8,6) = -e2s;
        E4 = diag(e4c*ones(8,1));
        E4(1,5) = -e4s; E4(2,6) = -e4s; E4(3,7) = -e4s; E4(4,8) = -e4s;
        E4(5,1) =  e4s; E4(6,2) =  e4s; E4(7,3) =  e4s; E4(8,4) =  e4s;
        y = y + E4 * (E2 * (E1 * x));
    end; end; end
    Y(k1+1,k2+1,k3+1) = octonion(y(1),y(2),y(3),y(4),y(5),y(6),y(7),y(8));
end; end; end