def vpermilps1 : instruction :=
  definst "vpermilps" $ do
    pattern fun (v_3107 : imm int) (v_3108 : reg (bv 128)) (v_3109 : reg (bv 128)) => do
      v_8259 <- eval (handleImmediateWithSignExtend v_3107 8 8);
      v_8260 <- eval (extract v_8259 0 2);
      v_8262 <- getRegister v_3108;
      v_8263 <- eval (extract v_8262 96 128);
      v_8265 <- eval (extract v_8262 64 96);
      v_8267 <- eval (extract v_8262 32 64);
      v_8268 <- eval (extract v_8262 0 32);
      v_8272 <- eval (extract v_8259 2 4);
      v_8279 <- eval (extract v_8259 4 6);
      v_8286 <- eval (extract v_8259 6 8);
      setRegister (lhs.of_reg v_3109) (concat (mux (eq v_8260 (expression.bv_nat 2 0)) v_8263 (mux (eq v_8260 (expression.bv_nat 2 1)) v_8265 (mux (eq v_8260 (expression.bv_nat 2 2)) v_8267 v_8268))) (concat (mux (eq v_8272 (expression.bv_nat 2 0)) v_8263 (mux (eq v_8272 (expression.bv_nat 2 1)) v_8265 (mux (eq v_8272 (expression.bv_nat 2 2)) v_8267 v_8268))) (concat (mux (eq v_8279 (expression.bv_nat 2 0)) v_8263 (mux (eq v_8279 (expression.bv_nat 2 1)) v_8265 (mux (eq v_8279 (expression.bv_nat 2 2)) v_8267 v_8268))) (mux (eq v_8286 (expression.bv_nat 2 0)) v_8263 (mux (eq v_8286 (expression.bv_nat 2 1)) v_8265 (mux (eq v_8286 (expression.bv_nat 2 2)) v_8267 v_8268))))));
      pure ()
    pat_end;
    pattern fun (v_3118 : reg (bv 128)) (v_3119 : reg (bv 128)) (v_3120 : reg (bv 128)) => do
      v_8302 <- getRegister v_3118;
      v_8303 <- eval (extract v_8302 30 32);
      v_8305 <- getRegister v_3119;
      v_8306 <- eval (extract v_8305 96 128);
      v_8308 <- eval (extract v_8305 64 96);
      v_8310 <- eval (extract v_8305 32 64);
      v_8311 <- eval (extract v_8305 0 32);
      v_8315 <- eval (extract v_8302 62 64);
      v_8322 <- eval (extract v_8302 94 96);
      v_8329 <- eval (extract v_8302 126 128);
      setRegister (lhs.of_reg v_3120) (concat (mux (eq v_8303 (expression.bv_nat 2 0)) v_8306 (mux (eq v_8303 (expression.bv_nat 2 1)) v_8308 (mux (eq v_8303 (expression.bv_nat 2 2)) v_8310 v_8311))) (concat (mux (eq v_8315 (expression.bv_nat 2 0)) v_8306 (mux (eq v_8315 (expression.bv_nat 2 1)) v_8308 (mux (eq v_8315 (expression.bv_nat 2 2)) v_8310 v_8311))) (concat (mux (eq v_8322 (expression.bv_nat 2 0)) v_8306 (mux (eq v_8322 (expression.bv_nat 2 1)) v_8308 (mux (eq v_8322 (expression.bv_nat 2 2)) v_8310 v_8311))) (mux (eq v_8329 (expression.bv_nat 2 0)) v_8306 (mux (eq v_8329 (expression.bv_nat 2 1)) v_8308 (mux (eq v_8329 (expression.bv_nat 2 2)) v_8310 v_8311))))));
      pure ()
    pat_end;
    pattern fun (v_3129 : imm int) (v_3130 : reg (bv 256)) (v_3131 : reg (bv 256)) => do
      v_8345 <- eval (handleImmediateWithSignExtend v_3129 8 8);
      v_8346 <- eval (extract v_8345 0 2);
      v_8347 <- eval (eq v_8346 (expression.bv_nat 2 0));
      v_8348 <- getRegister v_3130;
      v_8349 <- eval (extract v_8348 96 128);
      v_8350 <- eval (eq v_8346 (expression.bv_nat 2 1));
      v_8351 <- eval (extract v_8348 64 96);
      v_8352 <- eval (eq v_8346 (expression.bv_nat 2 2));
      v_8353 <- eval (extract v_8348 32 64);
      v_8354 <- eval (extract v_8348 0 32);
      v_8358 <- eval (extract v_8345 2 4);
      v_8359 <- eval (eq v_8358 (expression.bv_nat 2 0));
      v_8360 <- eval (eq v_8358 (expression.bv_nat 2 1));
      v_8361 <- eval (eq v_8358 (expression.bv_nat 2 2));
      v_8365 <- eval (extract v_8345 4 6);
      v_8366 <- eval (eq v_8365 (expression.bv_nat 2 0));
      v_8367 <- eval (eq v_8365 (expression.bv_nat 2 1));
      v_8368 <- eval (eq v_8365 (expression.bv_nat 2 2));
      v_8372 <- eval (extract v_8345 6 8);
      v_8373 <- eval (eq v_8372 (expression.bv_nat 2 0));
      v_8374 <- eval (eq v_8372 (expression.bv_nat 2 1));
      v_8375 <- eval (eq v_8372 (expression.bv_nat 2 2));
      v_8379 <- eval (extract v_8348 224 256);
      v_8380 <- eval (extract v_8348 192 224);
      v_8381 <- eval (extract v_8348 160 192);
      v_8382 <- eval (extract v_8348 128 160);
      setRegister (lhs.of_reg v_3131) (concat (mux v_8347 v_8349 (mux v_8350 v_8351 (mux v_8352 v_8353 v_8354))) (concat (mux v_8359 v_8349 (mux v_8360 v_8351 (mux v_8361 v_8353 v_8354))) (concat (mux v_8366 v_8349 (mux v_8367 v_8351 (mux v_8368 v_8353 v_8354))) (concat (mux v_8373 v_8349 (mux v_8374 v_8351 (mux v_8375 v_8353 v_8354))) (concat (mux v_8347 v_8379 (mux v_8350 v_8380 (mux v_8352 v_8381 v_8382))) (concat (mux v_8359 v_8379 (mux v_8360 v_8380 (mux v_8361 v_8381 v_8382))) (concat (mux v_8366 v_8379 (mux v_8367 v_8380 (mux v_8368 v_8381 v_8382))) (mux v_8373 v_8379 (mux v_8374 v_8380 (mux v_8375 v_8381 v_8382))))))))));
      pure ()
    pat_end;
    pattern fun (v_3140 : reg (bv 256)) (v_3141 : reg (bv 256)) (v_3142 : reg (bv 256)) => do
      v_8408 <- getRegister v_3140;
      v_8409 <- eval (extract v_8408 30 32);
      v_8411 <- getRegister v_3141;
      v_8412 <- eval (extract v_8411 96 128);
      v_8414 <- eval (extract v_8411 64 96);
      v_8416 <- eval (extract v_8411 32 64);
      v_8417 <- eval (extract v_8411 0 32);
      v_8421 <- eval (extract v_8408 62 64);
      v_8428 <- eval (extract v_8408 94 96);
      v_8435 <- eval (extract v_8408 126 128);
      v_8442 <- eval (extract v_8408 158 160);
      v_8444 <- eval (extract v_8411 224 256);
      v_8446 <- eval (extract v_8411 192 224);
      v_8448 <- eval (extract v_8411 160 192);
      v_8449 <- eval (extract v_8411 128 160);
      v_8453 <- eval (extract v_8408 190 192);
      v_8460 <- eval (extract v_8408 222 224);
      v_8467 <- eval (extract v_8408 254 256);
      setRegister (lhs.of_reg v_3142) (concat (mux (eq v_8409 (expression.bv_nat 2 0)) v_8412 (mux (eq v_8409 (expression.bv_nat 2 1)) v_8414 (mux (eq v_8409 (expression.bv_nat 2 2)) v_8416 v_8417))) (concat (mux (eq v_8421 (expression.bv_nat 2 0)) v_8412 (mux (eq v_8421 (expression.bv_nat 2 1)) v_8414 (mux (eq v_8421 (expression.bv_nat 2 2)) v_8416 v_8417))) (concat (mux (eq v_8428 (expression.bv_nat 2 0)) v_8412 (mux (eq v_8428 (expression.bv_nat 2 1)) v_8414 (mux (eq v_8428 (expression.bv_nat 2 2)) v_8416 v_8417))) (concat (mux (eq v_8435 (expression.bv_nat 2 0)) v_8412 (mux (eq v_8435 (expression.bv_nat 2 1)) v_8414 (mux (eq v_8435 (expression.bv_nat 2 2)) v_8416 v_8417))) (concat (mux (eq v_8442 (expression.bv_nat 2 0)) v_8444 (mux (eq v_8442 (expression.bv_nat 2 1)) v_8446 (mux (eq v_8442 (expression.bv_nat 2 2)) v_8448 v_8449))) (concat (mux (eq v_8453 (expression.bv_nat 2 0)) v_8444 (mux (eq v_8453 (expression.bv_nat 2 1)) v_8446 (mux (eq v_8453 (expression.bv_nat 2 2)) v_8448 v_8449))) (concat (mux (eq v_8460 (expression.bv_nat 2 0)) v_8444 (mux (eq v_8460 (expression.bv_nat 2 1)) v_8446 (mux (eq v_8460 (expression.bv_nat 2 2)) v_8448 v_8449))) (mux (eq v_8467 (expression.bv_nat 2 0)) v_8444 (mux (eq v_8467 (expression.bv_nat 2 1)) v_8446 (mux (eq v_8467 (expression.bv_nat 2 2)) v_8448 v_8449))))))))));
      pure ()
    pat_end;
    pattern fun (v_3103 : imm int) (v_3102 : Mem) (v_3104 : reg (bv 128)) => do
      v_16781 <- eval (handleImmediateWithSignExtend v_3103 8 8);
      v_16782 <- eval (extract v_16781 0 2);
      v_16784 <- evaluateAddress v_3102;
      v_16785 <- load v_16784 16;
      v_16786 <- eval (extract v_16785 96 128);
      v_16788 <- eval (extract v_16785 64 96);
      v_16790 <- eval (extract v_16785 32 64);
      v_16791 <- eval (extract v_16785 0 32);
      v_16795 <- eval (extract v_16781 2 4);
      v_16802 <- eval (extract v_16781 4 6);
      v_16809 <- eval (extract v_16781 6 8);
      setRegister (lhs.of_reg v_3104) (concat (mux (eq v_16782 (expression.bv_nat 2 0)) v_16786 (mux (eq v_16782 (expression.bv_nat 2 1)) v_16788 (mux (eq v_16782 (expression.bv_nat 2 2)) v_16790 v_16791))) (concat (mux (eq v_16795 (expression.bv_nat 2 0)) v_16786 (mux (eq v_16795 (expression.bv_nat 2 1)) v_16788 (mux (eq v_16795 (expression.bv_nat 2 2)) v_16790 v_16791))) (concat (mux (eq v_16802 (expression.bv_nat 2 0)) v_16786 (mux (eq v_16802 (expression.bv_nat 2 1)) v_16788 (mux (eq v_16802 (expression.bv_nat 2 2)) v_16790 v_16791))) (mux (eq v_16809 (expression.bv_nat 2 0)) v_16786 (mux (eq v_16809 (expression.bv_nat 2 1)) v_16788 (mux (eq v_16809 (expression.bv_nat 2 2)) v_16790 v_16791))))));
      pure ()
    pat_end;
    pattern fun (v_3113 : Mem) (v_3114 : reg (bv 128)) (v_3115 : reg (bv 128)) => do
      v_16820 <- evaluateAddress v_3113;
      v_16821 <- load v_16820 16;
      v_16822 <- eval (extract v_16821 30 32);
      v_16824 <- getRegister v_3114;
      v_16825 <- eval (extract v_16824 96 128);
      v_16827 <- eval (extract v_16824 64 96);
      v_16829 <- eval (extract v_16824 32 64);
      v_16830 <- eval (extract v_16824 0 32);
      v_16834 <- eval (extract v_16821 62 64);
      v_16841 <- eval (extract v_16821 94 96);
      v_16848 <- eval (extract v_16821 126 128);
      setRegister (lhs.of_reg v_3115) (concat (mux (eq v_16822 (expression.bv_nat 2 0)) v_16825 (mux (eq v_16822 (expression.bv_nat 2 1)) v_16827 (mux (eq v_16822 (expression.bv_nat 2 2)) v_16829 v_16830))) (concat (mux (eq v_16834 (expression.bv_nat 2 0)) v_16825 (mux (eq v_16834 (expression.bv_nat 2 1)) v_16827 (mux (eq v_16834 (expression.bv_nat 2 2)) v_16829 v_16830))) (concat (mux (eq v_16841 (expression.bv_nat 2 0)) v_16825 (mux (eq v_16841 (expression.bv_nat 2 1)) v_16827 (mux (eq v_16841 (expression.bv_nat 2 2)) v_16829 v_16830))) (mux (eq v_16848 (expression.bv_nat 2 0)) v_16825 (mux (eq v_16848 (expression.bv_nat 2 1)) v_16827 (mux (eq v_16848 (expression.bv_nat 2 2)) v_16829 v_16830))))));
      pure ()
    pat_end;
    pattern fun (v_3125 : imm int) (v_3124 : Mem) (v_3126 : reg (bv 256)) => do
      v_16859 <- eval (handleImmediateWithSignExtend v_3125 8 8);
      v_16860 <- eval (extract v_16859 0 2);
      v_16861 <- eval (eq v_16860 (expression.bv_nat 2 0));
      v_16862 <- evaluateAddress v_3124;
      v_16863 <- load v_16862 32;
      v_16864 <- eval (extract v_16863 96 128);
      v_16865 <- eval (eq v_16860 (expression.bv_nat 2 1));
      v_16866 <- eval (extract v_16863 64 96);
      v_16867 <- eval (eq v_16860 (expression.bv_nat 2 2));
      v_16868 <- eval (extract v_16863 32 64);
      v_16869 <- eval (extract v_16863 0 32);
      v_16873 <- eval (extract v_16859 2 4);
      v_16874 <- eval (eq v_16873 (expression.bv_nat 2 0));
      v_16875 <- eval (eq v_16873 (expression.bv_nat 2 1));
      v_16876 <- eval (eq v_16873 (expression.bv_nat 2 2));
      v_16880 <- eval (extract v_16859 4 6);
      v_16881 <- eval (eq v_16880 (expression.bv_nat 2 0));
      v_16882 <- eval (eq v_16880 (expression.bv_nat 2 1));
      v_16883 <- eval (eq v_16880 (expression.bv_nat 2 2));
      v_16887 <- eval (extract v_16859 6 8);
      v_16888 <- eval (eq v_16887 (expression.bv_nat 2 0));
      v_16889 <- eval (eq v_16887 (expression.bv_nat 2 1));
      v_16890 <- eval (eq v_16887 (expression.bv_nat 2 2));
      v_16894 <- eval (extract v_16863 224 256);
      v_16895 <- eval (extract v_16863 192 224);
      v_16896 <- eval (extract v_16863 160 192);
      v_16897 <- eval (extract v_16863 128 160);
      setRegister (lhs.of_reg v_3126) (concat (mux v_16861 v_16864 (mux v_16865 v_16866 (mux v_16867 v_16868 v_16869))) (concat (mux v_16874 v_16864 (mux v_16875 v_16866 (mux v_16876 v_16868 v_16869))) (concat (mux v_16881 v_16864 (mux v_16882 v_16866 (mux v_16883 v_16868 v_16869))) (concat (mux v_16888 v_16864 (mux v_16889 v_16866 (mux v_16890 v_16868 v_16869))) (concat (mux v_16861 v_16894 (mux v_16865 v_16895 (mux v_16867 v_16896 v_16897))) (concat (mux v_16874 v_16894 (mux v_16875 v_16895 (mux v_16876 v_16896 v_16897))) (concat (mux v_16881 v_16894 (mux v_16882 v_16895 (mux v_16883 v_16896 v_16897))) (mux v_16888 v_16894 (mux v_16889 v_16895 (mux v_16890 v_16896 v_16897))))))))));
      pure ()
    pat_end;
    pattern fun (v_3135 : Mem) (v_3136 : reg (bv 256)) (v_3137 : reg (bv 256)) => do
      v_16918 <- evaluateAddress v_3135;
      v_16919 <- load v_16918 32;
      v_16920 <- eval (extract v_16919 30 32);
      v_16922 <- getRegister v_3136;
      v_16923 <- eval (extract v_16922 96 128);
      v_16925 <- eval (extract v_16922 64 96);
      v_16927 <- eval (extract v_16922 32 64);
      v_16928 <- eval (extract v_16922 0 32);
      v_16932 <- eval (extract v_16919 62 64);
      v_16939 <- eval (extract v_16919 94 96);
      v_16946 <- eval (extract v_16919 126 128);
      v_16953 <- eval (extract v_16919 158 160);
      v_16955 <- eval (extract v_16922 224 256);
      v_16957 <- eval (extract v_16922 192 224);
      v_16959 <- eval (extract v_16922 160 192);
      v_16960 <- eval (extract v_16922 128 160);
      v_16964 <- eval (extract v_16919 190 192);
      v_16971 <- eval (extract v_16919 222 224);
      v_16978 <- eval (extract v_16919 254 256);
      setRegister (lhs.of_reg v_3137) (concat (mux (eq v_16920 (expression.bv_nat 2 0)) v_16923 (mux (eq v_16920 (expression.bv_nat 2 1)) v_16925 (mux (eq v_16920 (expression.bv_nat 2 2)) v_16927 v_16928))) (concat (mux (eq v_16932 (expression.bv_nat 2 0)) v_16923 (mux (eq v_16932 (expression.bv_nat 2 1)) v_16925 (mux (eq v_16932 (expression.bv_nat 2 2)) v_16927 v_16928))) (concat (mux (eq v_16939 (expression.bv_nat 2 0)) v_16923 (mux (eq v_16939 (expression.bv_nat 2 1)) v_16925 (mux (eq v_16939 (expression.bv_nat 2 2)) v_16927 v_16928))) (concat (mux (eq v_16946 (expression.bv_nat 2 0)) v_16923 (mux (eq v_16946 (expression.bv_nat 2 1)) v_16925 (mux (eq v_16946 (expression.bv_nat 2 2)) v_16927 v_16928))) (concat (mux (eq v_16953 (expression.bv_nat 2 0)) v_16955 (mux (eq v_16953 (expression.bv_nat 2 1)) v_16957 (mux (eq v_16953 (expression.bv_nat 2 2)) v_16959 v_16960))) (concat (mux (eq v_16964 (expression.bv_nat 2 0)) v_16955 (mux (eq v_16964 (expression.bv_nat 2 1)) v_16957 (mux (eq v_16964 (expression.bv_nat 2 2)) v_16959 v_16960))) (concat (mux (eq v_16971 (expression.bv_nat 2 0)) v_16955 (mux (eq v_16971 (expression.bv_nat 2 1)) v_16957 (mux (eq v_16971 (expression.bv_nat 2 2)) v_16959 v_16960))) (mux (eq v_16978 (expression.bv_nat 2 0)) v_16955 (mux (eq v_16978 (expression.bv_nat 2 1)) v_16957 (mux (eq v_16978 (expression.bv_nat 2 2)) v_16959 v_16960))))))))));
      pure ()
    pat_end
