def psignb1 : instruction :=
  definst "psignb" $ do
    pattern fun (v_3023 : reg (bv 128)) (v_3024 : reg (bv 128)) => do
      v_7292 <- getRegister v_3023;
      v_7293 <- eval (extract v_7292 0 8);
      v_7295 <- getRegister v_3024;
      v_7296 <- eval (extract v_7295 0 8);
      v_7302 <- eval (extract v_7292 8 16);
      v_7304 <- eval (extract v_7295 8 16);
      v_7310 <- eval (extract v_7292 16 24);
      v_7312 <- eval (extract v_7295 16 24);
      v_7318 <- eval (extract v_7292 24 32);
      v_7320 <- eval (extract v_7295 24 32);
      v_7326 <- eval (extract v_7292 32 40);
      v_7328 <- eval (extract v_7295 32 40);
      v_7334 <- eval (extract v_7292 40 48);
      v_7336 <- eval (extract v_7295 40 48);
      v_7342 <- eval (extract v_7292 48 56);
      v_7344 <- eval (extract v_7295 48 56);
      v_7350 <- eval (extract v_7292 56 64);
      v_7352 <- eval (extract v_7295 56 64);
      v_7358 <- eval (extract v_7292 64 72);
      v_7360 <- eval (extract v_7295 64 72);
      v_7366 <- eval (extract v_7292 72 80);
      v_7368 <- eval (extract v_7295 72 80);
      v_7374 <- eval (extract v_7292 80 88);
      v_7376 <- eval (extract v_7295 80 88);
      v_7382 <- eval (extract v_7292 88 96);
      v_7384 <- eval (extract v_7295 88 96);
      v_7390 <- eval (extract v_7292 96 104);
      v_7392 <- eval (extract v_7295 96 104);
      v_7398 <- eval (extract v_7292 104 112);
      v_7400 <- eval (extract v_7295 104 112);
      v_7406 <- eval (extract v_7292 112 120);
      v_7408 <- eval (extract v_7295 112 120);
      v_7414 <- eval (extract v_7292 120 128);
      v_7416 <- eval (extract v_7295 120 128);
      setRegister (lhs.of_reg v_3024) (concat (mux (sgt v_7293 (expression.bv_nat 8 0)) v_7296 (mux (eq v_7293 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7296 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7302 (expression.bv_nat 8 0)) v_7304 (mux (eq v_7302 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7304 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7310 (expression.bv_nat 8 0)) v_7312 (mux (eq v_7310 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7312 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7318 (expression.bv_nat 8 0)) v_7320 (mux (eq v_7318 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7320 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7326 (expression.bv_nat 8 0)) v_7328 (mux (eq v_7326 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7328 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7334 (expression.bv_nat 8 0)) v_7336 (mux (eq v_7334 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7336 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7342 (expression.bv_nat 8 0)) v_7344 (mux (eq v_7342 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7344 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7350 (expression.bv_nat 8 0)) v_7352 (mux (eq v_7350 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7352 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7358 (expression.bv_nat 8 0)) v_7360 (mux (eq v_7358 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7360 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7366 (expression.bv_nat 8 0)) v_7368 (mux (eq v_7366 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7368 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7374 (expression.bv_nat 8 0)) v_7376 (mux (eq v_7374 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7376 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7382 (expression.bv_nat 8 0)) v_7384 (mux (eq v_7382 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7384 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7390 (expression.bv_nat 8 0)) v_7392 (mux (eq v_7390 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7392 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7398 (expression.bv_nat 8 0)) v_7400 (mux (eq v_7398 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7400 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7406 (expression.bv_nat 8 0)) v_7408 (mux (eq v_7406 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7408 (expression.bv_nat 8 255))))) (mux (sgt v_7414 (expression.bv_nat 8 0)) v_7416 (mux (eq v_7414 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7416 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3019 : Mem) (v_3020 : reg (bv 128)) => do
      v_13954 <- evaluateAddress v_3019;
      v_13955 <- load v_13954 16;
      v_13956 <- eval (extract v_13955 0 8);
      v_13958 <- getRegister v_3020;
      v_13959 <- eval (extract v_13958 0 8);
      v_13965 <- eval (extract v_13955 8 16);
      v_13967 <- eval (extract v_13958 8 16);
      v_13973 <- eval (extract v_13955 16 24);
      v_13975 <- eval (extract v_13958 16 24);
      v_13981 <- eval (extract v_13955 24 32);
      v_13983 <- eval (extract v_13958 24 32);
      v_13989 <- eval (extract v_13955 32 40);
      v_13991 <- eval (extract v_13958 32 40);
      v_13997 <- eval (extract v_13955 40 48);
      v_13999 <- eval (extract v_13958 40 48);
      v_14005 <- eval (extract v_13955 48 56);
      v_14007 <- eval (extract v_13958 48 56);
      v_14013 <- eval (extract v_13955 56 64);
      v_14015 <- eval (extract v_13958 56 64);
      v_14021 <- eval (extract v_13955 64 72);
      v_14023 <- eval (extract v_13958 64 72);
      v_14029 <- eval (extract v_13955 72 80);
      v_14031 <- eval (extract v_13958 72 80);
      v_14037 <- eval (extract v_13955 80 88);
      v_14039 <- eval (extract v_13958 80 88);
      v_14045 <- eval (extract v_13955 88 96);
      v_14047 <- eval (extract v_13958 88 96);
      v_14053 <- eval (extract v_13955 96 104);
      v_14055 <- eval (extract v_13958 96 104);
      v_14061 <- eval (extract v_13955 104 112);
      v_14063 <- eval (extract v_13958 104 112);
      v_14069 <- eval (extract v_13955 112 120);
      v_14071 <- eval (extract v_13958 112 120);
      v_14077 <- eval (extract v_13955 120 128);
      v_14079 <- eval (extract v_13958 120 128);
      setRegister (lhs.of_reg v_3020) (concat (mux (sgt v_13956 (expression.bv_nat 8 0)) v_13959 (mux (eq v_13956 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13959 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13965 (expression.bv_nat 8 0)) v_13967 (mux (eq v_13965 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13967 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13973 (expression.bv_nat 8 0)) v_13975 (mux (eq v_13973 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13975 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13981 (expression.bv_nat 8 0)) v_13983 (mux (eq v_13981 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13983 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13989 (expression.bv_nat 8 0)) v_13991 (mux (eq v_13989 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13991 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13997 (expression.bv_nat 8 0)) v_13999 (mux (eq v_13997 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13999 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14005 (expression.bv_nat 8 0)) v_14007 (mux (eq v_14005 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14007 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14013 (expression.bv_nat 8 0)) v_14015 (mux (eq v_14013 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14015 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14021 (expression.bv_nat 8 0)) v_14023 (mux (eq v_14021 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14023 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14029 (expression.bv_nat 8 0)) v_14031 (mux (eq v_14029 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14031 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14037 (expression.bv_nat 8 0)) v_14039 (mux (eq v_14037 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14039 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14045 (expression.bv_nat 8 0)) v_14047 (mux (eq v_14045 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14047 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14053 (expression.bv_nat 8 0)) v_14055 (mux (eq v_14053 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14055 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14061 (expression.bv_nat 8 0)) v_14063 (mux (eq v_14061 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14063 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14069 (expression.bv_nat 8 0)) v_14071 (mux (eq v_14069 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14071 (expression.bv_nat 8 255))))) (mux (sgt v_14077 (expression.bv_nat 8 0)) v_14079 (mux (eq v_14077 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14079 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end
