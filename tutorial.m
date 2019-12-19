%% OCTONION FOURIER TRANSFORM tutorial
%%
% Functions offt3 and iofft3 implement the octonion Fourier transform
% (forward and inverse). The qtfm (http://qtfm.sourceforge.net) package is 
% required in order to use those functions. The argument of offt3 and 
% iofft3 must be of an octonion type. 

% We create sample 3-dimensional octonion matrix:
N = 4;
u = octonion(...
    rand(N,N,N), rand(N,N,N), rand(N,N,N), rand(N,N,N), ...
    rand(N,N,N), rand(N,N,N), rand(N,N,N), rand(N,N,N));

% And calculate its OFT with two different algorithms:
U1 = offt3(u);              % FFT-based implementation
U2 = doft3(u);              % direct formula-based implementation

%%
% We check the correctness of implemented functions by comparing outputs of
% two different algorithms:
dif = zeros(1,8);
for i = 1:8
    dif(i) = max(abs(part(U1(:)-U2(:),i)./part(U2(:),i)));
end
disp(max(dif)*100)          % relative error of OFFT3 function

%%
% The other way to check the correctness of FFT-based algorithm (by
% calculating the inverse transform):
v1 = iofft3(U1);
err1 = u-v1;
dif = zeros(1,8);
for i = 1:8
    dif(i) = max(abs(part(err1(:),i)./part(u(:),i)));
end
disp(max(dif)*100)          % relative error of reconstruction

%%
% Checking the correctness of direct formula-based algorithm (by
% calculating the inverse transform):
v2 = idoft3(U2);
err = u-v2;
dif = zeros(1,8);
for i = 1:8
    dif(i) = max(abs(part(err(:),i)./part(u(:),i)));
end
disp(max(dif)*100)          % relative error of reconstruction

%%
% We check if the OFFT has the symmetry properties stated in literature.
% We create sample 3-dimensional octonion matrix (with real values):
N = 32;
u = dc(dc(randi(9,N,N,N), zeros(N,N,N)), zeros(N,N,N));

% And calculate its OFT with FFT-based algorithm:
U = offt3(u);

% We check the symmetry with respect to 1st, 2nd and 3rd variable
dif1 = fftreflection(U,1) + alpha(U,1,3,5,7);
dif2 = fftreflection(U,2) + alpha(U,2,3,6,7);
dif3 = fftreflection(U,3) + alpha(U,4,5,6,7);
                            % absolute difference
disp([max(abs(dif1(:))), max(abs(dif2(:))), max(abs(dif3(:)))])
