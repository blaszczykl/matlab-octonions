function Y = fftreflection(X, A)
% FFTREFLECTION Reflect the OFT spectrum with respect to some variable
% 
% This function rearranges an octonion Fourier transform X by reflecting 
% the spectrum with respect to variables with indices in vector A. It
% uses the convention that zero frequencies appear on the first coordinates
% of the matrix. 
% 
% See also: OFFT3, IOFFT3

narginchk(2, 2), nargoutchk(0, 1)

if ndims(X) ~= 3
    error('The transformed matrix must be 3-dimensional.');
end

if ~all(mod(A,1) == 0) || ~all(A >= 1) || ~all(A <= 3)
    error('A must be an array containing only 1s, 2s and 3s.');
end

Y = X;
for dim = A
    switch dim
        case 1
            Y(2:end,:,:) = flip(Y(2:end,:,:), 1);
        case 2
            Y(:,2:end,:) = flip(Y(:,2:end,:), 2);
        case 3
            Y(:,:,2:end) = flip(Y(:,:,2:end), 3);
    end
end