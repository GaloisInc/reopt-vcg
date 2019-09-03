def vpsignb1 : instruction :=
  definst "vpsignb" $ do
    pattern fun (v_3018 : reg (bv 128)) (v_3019 : reg (bv 128)) (v_3020 : reg (bv 128)) => do
      v_7330 <- getRegister v_3018;
      v_7331 <- eval (extract v_7330 0 8);
      v_7333 <- getRegister v_3019;
      v_7334 <- eval (extract v_7333 0 8);
      v_7340 <- eval (extract v_7330 8 16);
      v_7342 <- eval (extract v_7333 8 16);
      v_7348 <- eval (extract v_7330 16 24);
      v_7350 <- eval (extract v_7333 16 24);
      v_7356 <- eval (extract v_7330 24 32);
      v_7358 <- eval (extract v_7333 24 32);
      v_7364 <- eval (extract v_7330 32 40);
      v_7366 <- eval (extract v_7333 32 40);
      v_7372 <- eval (extract v_7330 40 48);
      v_7374 <- eval (extract v_7333 40 48);
      v_7380 <- eval (extract v_7330 48 56);
      v_7382 <- eval (extract v_7333 48 56);
      v_7388 <- eval (extract v_7330 56 64);
      v_7390 <- eval (extract v_7333 56 64);
      v_7396 <- eval (extract v_7330 64 72);
      v_7398 <- eval (extract v_7333 64 72);
      v_7404 <- eval (extract v_7330 72 80);
      v_7406 <- eval (extract v_7333 72 80);
      v_7412 <- eval (extract v_7330 80 88);
      v_7414 <- eval (extract v_7333 80 88);
      v_7420 <- eval (extract v_7330 88 96);
      v_7422 <- eval (extract v_7333 88 96);
      v_7428 <- eval (extract v_7330 96 104);
      v_7430 <- eval (extract v_7333 96 104);
      v_7436 <- eval (extract v_7330 104 112);
      v_7438 <- eval (extract v_7333 104 112);
      v_7444 <- eval (extract v_7330 112 120);
      v_7446 <- eval (extract v_7333 112 120);
      v_7452 <- eval (extract v_7330 120 128);
      v_7454 <- eval (extract v_7333 120 128);
      setRegister (lhs.of_reg v_3020) (concat (mux (sgt v_7331 (expression.bv_nat 8 0)) v_7334 (mux (eq v_7331 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7334 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7340 (expression.bv_nat 8 0)) v_7342 (mux (eq v_7340 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7342 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7348 (expression.bv_nat 8 0)) v_7350 (mux (eq v_7348 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7350 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7356 (expression.bv_nat 8 0)) v_7358 (mux (eq v_7356 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7358 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7364 (expression.bv_nat 8 0)) v_7366 (mux (eq v_7364 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7366 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7372 (expression.bv_nat 8 0)) v_7374 (mux (eq v_7372 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7374 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7380 (expression.bv_nat 8 0)) v_7382 (mux (eq v_7380 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7382 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7388 (expression.bv_nat 8 0)) v_7390 (mux (eq v_7388 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7390 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7396 (expression.bv_nat 8 0)) v_7398 (mux (eq v_7396 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7398 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7404 (expression.bv_nat 8 0)) v_7406 (mux (eq v_7404 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7406 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7412 (expression.bv_nat 8 0)) v_7414 (mux (eq v_7412 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7414 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7420 (expression.bv_nat 8 0)) v_7422 (mux (eq v_7420 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7422 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7428 (expression.bv_nat 8 0)) v_7430 (mux (eq v_7428 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7430 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7436 (expression.bv_nat 8 0)) v_7438 (mux (eq v_7436 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7438 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7444 (expression.bv_nat 8 0)) v_7446 (mux (eq v_7444 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7446 (expression.bv_nat 8 255))))) (mux (sgt v_7452 (expression.bv_nat 8 0)) v_7454 (mux (eq v_7452 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7454 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3012 : Mem) (v_3013 : reg (bv 128)) (v_3014 : reg (bv 128)) => do
      v_13872 <- evaluateAddress v_3012;
      v_13873 <- load v_13872 16;
      v_13874 <- eval (extract v_13873 0 8);
      v_13876 <- getRegister v_3013;
      v_13877 <- eval (extract v_13876 0 8);
      v_13883 <- eval (extract v_13873 8 16);
      v_13885 <- eval (extract v_13876 8 16);
      v_13891 <- eval (extract v_13873 16 24);
      v_13893 <- eval (extract v_13876 16 24);
      v_13899 <- eval (extract v_13873 24 32);
      v_13901 <- eval (extract v_13876 24 32);
      v_13907 <- eval (extract v_13873 32 40);
      v_13909 <- eval (extract v_13876 32 40);
      v_13915 <- eval (extract v_13873 40 48);
      v_13917 <- eval (extract v_13876 40 48);
      v_13923 <- eval (extract v_13873 48 56);
      v_13925 <- eval (extract v_13876 48 56);
      v_13931 <- eval (extract v_13873 56 64);
      v_13933 <- eval (extract v_13876 56 64);
      v_13939 <- eval (extract v_13873 64 72);
      v_13941 <- eval (extract v_13876 64 72);
      v_13947 <- eval (extract v_13873 72 80);
      v_13949 <- eval (extract v_13876 72 80);
      v_13955 <- eval (extract v_13873 80 88);
      v_13957 <- eval (extract v_13876 80 88);
      v_13963 <- eval (extract v_13873 88 96);
      v_13965 <- eval (extract v_13876 88 96);
      v_13971 <- eval (extract v_13873 96 104);
      v_13973 <- eval (extract v_13876 96 104);
      v_13979 <- eval (extract v_13873 104 112);
      v_13981 <- eval (extract v_13876 104 112);
      v_13987 <- eval (extract v_13873 112 120);
      v_13989 <- eval (extract v_13876 112 120);
      v_13995 <- eval (extract v_13873 120 128);
      v_13997 <- eval (extract v_13876 120 128);
      setRegister (lhs.of_reg v_3014) (concat (mux (sgt v_13874 (expression.bv_nat 8 0)) v_13877 (mux (eq v_13874 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13877 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13883 (expression.bv_nat 8 0)) v_13885 (mux (eq v_13883 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13885 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13891 (expression.bv_nat 8 0)) v_13893 (mux (eq v_13891 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13893 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13899 (expression.bv_nat 8 0)) v_13901 (mux (eq v_13899 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13901 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13907 (expression.bv_nat 8 0)) v_13909 (mux (eq v_13907 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13909 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13915 (expression.bv_nat 8 0)) v_13917 (mux (eq v_13915 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13917 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13923 (expression.bv_nat 8 0)) v_13925 (mux (eq v_13923 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13925 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13931 (expression.bv_nat 8 0)) v_13933 (mux (eq v_13931 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13933 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13939 (expression.bv_nat 8 0)) v_13941 (mux (eq v_13939 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13941 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13947 (expression.bv_nat 8 0)) v_13949 (mux (eq v_13947 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13949 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13955 (expression.bv_nat 8 0)) v_13957 (mux (eq v_13955 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13957 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13963 (expression.bv_nat 8 0)) v_13965 (mux (eq v_13963 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13965 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13971 (expression.bv_nat 8 0)) v_13973 (mux (eq v_13971 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13973 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13979 (expression.bv_nat 8 0)) v_13981 (mux (eq v_13979 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13981 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13987 (expression.bv_nat 8 0)) v_13989 (mux (eq v_13987 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13989 (expression.bv_nat 8 255))))) (mux (sgt v_13995 (expression.bv_nat 8 0)) v_13997 (mux (eq v_13995 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13997 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end
