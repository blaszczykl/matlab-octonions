function Y = offt3(X)
% OFFT Discrete octonion Fourier transform
% 
% This function calculates the fast octonion Fourier transform of
% 3-dimensional matrix X. 
% 
% See also: IOFFT

narginchk(1, 1), nargoutchk(0, 1)

if ~isreal(X)
    error('The transformed matrix must have components that are real octonions.');
end

if ndims(X) ~= 3
    error('The transformed matrix must be 3-dimensional.');
end

e2 = octonion(0,0,1,0,0,0,0,0);
e4 = octonion(0,0,0,0,1,0,0,0);

Y = octonion(zeros(size(X)));
for i = 1:4
    Ca = fftn(complex(part(X,2*i-1), part(X,2*i)));
        Cb = fftreflection(Ca, 2);
        Cc = fftreflection(Ca, 3);
        Cd = fftreflection(Cb, 3);
    V = octonion( real(Ca) + real(Cb) + real(Cc) + real(Cd),...
                  imag(Ca) + imag(Cb) + imag(Cc) + imag(Cd),...
                  imag(Ca) - imag(Cb) + imag(Cc) - imag(Cd),...
                 -real(Ca) + real(Cb) - real(Cc) + real(Cd),...
                  imag(Ca) + imag(Cb) - imag(Cc) - imag(Cd),...
                 -real(Ca) - real(Cb) + real(Cc) + real(Cd),...
                 -real(Ca) + real(Cb) + real(Cc) - real(Cd),...
                 -imag(Ca) + imag(Cb) + imag(Cc) - imag(Cd));
    switch i
        case 1
            Y = Y +  V;
        case 2
            Y = Y +  fftreflection(V,[1,3]) * e2;
        case 3
            Y = Y +  fftreflection(V,[1,2]) * e4;
        case 4
            Y = Y + (fftreflection(V,[2,3]) * e2) * e4;
    end
end
Y = Y / 4;