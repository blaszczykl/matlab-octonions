function Y = iofft3(X)
% IOFFT3 Inverse discrete octonion Fourier transform calculated with FFT 
% algorithm
% 
% This function calculates the inverse discrete octonion Fourier transform 
% of 3-dimensional octonion-valued matrix X using classical FFT algorithm.
% It uses the convention that zero frequencies appear on the first 
% coordinates of the matrix. In order to shift the zero frequency back to
% the first coordinates, the ifftshift function should be applied.
% 
% See also: OFFT3, IFFTSHIFT

narginchk(1, 1), nargoutchk(0, 1)

if ~isreal(X)
    error(['The transformed matrix must have components that are ', ...
        'real octonions.']);
end

if ndims(X) ~= 3
    error('The transformed matrix must be 3-dimensional.');
end

e1 = octonion(0,1,0,0,0,0,0,0);
e2 = octonion(0,0,1,0,0,0,0,0);

Y = octonion(zeros(size(X)));
for i = 1:4
    if i == 1 || i == 4
        Ca = ifftn(complex( part(X,i), part(X,i+4)));
    else
        Ca = ifftn(complex( part(X,i),-part(X,i+4)));
    end
        Cb = fftreflection(Ca, 2);
        Cc = fftreflection(Ca, 1);
        Cd = fftreflection(Cb, 1);
    V = octonion( real(Ca) + real(Cb) + real(Cc) + real(Cd),...
                  imag(Ca) + imag(Cb) - imag(Cc) - imag(Cd),...
                  imag(Ca) - imag(Cb) + imag(Cc) - imag(Cd),...
                  real(Ca) - real(Cb) - real(Cc) + real(Cd),...
                  imag(Ca) + imag(Cb) + imag(Cc) + imag(Cd),...
                  real(Ca) + real(Cb) - real(Cc) - real(Cd),...
                  real(Ca) - real(Cb) + real(Cc) - real(Cd),...
                  imag(Ca) - imag(Cb) - imag(Cc) + imag(Cd));
    switch i
        case 1
            Y = Y +  V;
        case 2
            Y = Y +  fftreflection(V,[2,3]) * e1;
        case 3
            Y = Y +  fftreflection(V,[1,3]) * e2;
        case 4
            Y = Y + (fftreflection(V,[1,2]) * e1) * e2;
    end
end
Y = Y / 4;