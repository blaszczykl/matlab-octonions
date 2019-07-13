function Y = fftreflection(X, A)

narginchk(2, 2), nargoutchk(0, 1)

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