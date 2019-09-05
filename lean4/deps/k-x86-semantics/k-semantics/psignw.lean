def psignw1 : instruction :=
  definst "psignw" $ do
    pattern fun (v_3013 : reg (bv 128)) (v_3014 : reg (bv 128)) => do
      v_7457 <- getRegister v_3013;
      v_7458 <- eval (extract v_7457 0 16);
      v_7460 <- getRegister v_3014;
      v_7461 <- eval (extract v_7460 0 16);
      v_7467 <- eval (extract v_7457 16 32);
      v_7469 <- eval (extract v_7460 16 32);
      v_7475 <- eval (extract v_7457 32 48);
      v_7477 <- eval (extract v_7460 32 48);
      v_7483 <- eval (extract v_7457 48 64);
      v_7485 <- eval (extract v_7460 48 64);
      v_7491 <- eval (extract v_7457 64 80);
      v_7493 <- eval (extract v_7460 64 80);
      v_7499 <- eval (extract v_7457 80 96);
      v_7501 <- eval (extract v_7460 80 96);
      v_7507 <- eval (extract v_7457 96 112);
      v_7509 <- eval (extract v_7460 96 112);
      v_7515 <- eval (extract v_7457 112 128);
      v_7517 <- eval (extract v_7460 112 128);
      setRegister (lhs.of_reg v_3014) (concat (mux (sgt v_7458 (expression.bv_nat 16 0)) v_7461 (mux (eq v_7458 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7461 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7467 (expression.bv_nat 16 0)) v_7469 (mux (eq v_7467 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7469 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7475 (expression.bv_nat 16 0)) v_7477 (mux (eq v_7475 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7477 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7483 (expression.bv_nat 16 0)) v_7485 (mux (eq v_7483 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7485 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7491 (expression.bv_nat 16 0)) v_7493 (mux (eq v_7491 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7493 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7499 (expression.bv_nat 16 0)) v_7501 (mux (eq v_7499 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7501 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7507 (expression.bv_nat 16 0)) v_7509 (mux (eq v_7507 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7509 (expression.bv_nat 16 65535))))) (mux (sgt v_7515 (expression.bv_nat 16 0)) v_7517 (mux (eq v_7515 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7517 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3010 : Mem) (v_3009 : reg (bv 128)) => do
      v_14164 <- evaluateAddress v_3010;
      v_14165 <- load v_14164 16;
      v_14166 <- eval (extract v_14165 0 16);
      v_14168 <- getRegister v_3009;
      v_14169 <- eval (extract v_14168 0 16);
      v_14175 <- eval (extract v_14165 16 32);
      v_14177 <- eval (extract v_14168 16 32);
      v_14183 <- eval (extract v_14165 32 48);
      v_14185 <- eval (extract v_14168 32 48);
      v_14191 <- eval (extract v_14165 48 64);
      v_14193 <- eval (extract v_14168 48 64);
      v_14199 <- eval (extract v_14165 64 80);
      v_14201 <- eval (extract v_14168 64 80);
      v_14207 <- eval (extract v_14165 80 96);
      v_14209 <- eval (extract v_14168 80 96);
      v_14215 <- eval (extract v_14165 96 112);
      v_14217 <- eval (extract v_14168 96 112);
      v_14223 <- eval (extract v_14165 112 128);
      v_14225 <- eval (extract v_14168 112 128);
      setRegister (lhs.of_reg v_3009) (concat (mux (sgt v_14166 (expression.bv_nat 16 0)) v_14169 (mux (eq v_14166 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14169 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14175 (expression.bv_nat 16 0)) v_14177 (mux (eq v_14175 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14177 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14183 (expression.bv_nat 16 0)) v_14185 (mux (eq v_14183 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14185 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14191 (expression.bv_nat 16 0)) v_14193 (mux (eq v_14191 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14193 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14199 (expression.bv_nat 16 0)) v_14201 (mux (eq v_14199 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14201 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14207 (expression.bv_nat 16 0)) v_14209 (mux (eq v_14207 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14209 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14215 (expression.bv_nat 16 0)) v_14217 (mux (eq v_14215 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14217 (expression.bv_nat 16 65535))))) (mux (sgt v_14223 (expression.bv_nat 16 0)) v_14225 (mux (eq v_14223 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14225 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end
