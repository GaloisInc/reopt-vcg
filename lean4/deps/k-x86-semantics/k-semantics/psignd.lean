def psignd1 : instruction :=
  definst "psignd" $ do
    pattern fun (v_3004 : reg (bv 128)) (v_3005 : reg (bv 128)) => do
      v_7415 <- getRegister v_3004;
      v_7416 <- eval (extract v_7415 0 32);
      v_7418 <- getRegister v_3005;
      v_7419 <- eval (extract v_7418 0 32);
      v_7425 <- eval (extract v_7415 32 64);
      v_7427 <- eval (extract v_7418 32 64);
      v_7433 <- eval (extract v_7415 64 96);
      v_7435 <- eval (extract v_7418 64 96);
      v_7441 <- eval (extract v_7415 96 128);
      v_7443 <- eval (extract v_7418 96 128);
      setRegister (lhs.of_reg v_3005) (concat (mux (sgt v_7416 (expression.bv_nat 32 0)) v_7419 (mux (eq v_7416 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7419 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7425 (expression.bv_nat 32 0)) v_7427 (mux (eq v_7425 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7427 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7433 (expression.bv_nat 32 0)) v_7435 (mux (eq v_7433 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7435 (expression.bv_nat 32 4294967295))))) (mux (sgt v_7441 (expression.bv_nat 32 0)) v_7443 (mux (eq v_7441 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7443 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end;
    pattern fun (v_3001 : Mem) (v_3000 : reg (bv 128)) => do
      v_14125 <- evaluateAddress v_3001;
      v_14126 <- load v_14125 16;
      v_14127 <- eval (extract v_14126 0 32);
      v_14129 <- getRegister v_3000;
      v_14130 <- eval (extract v_14129 0 32);
      v_14136 <- eval (extract v_14126 32 64);
      v_14138 <- eval (extract v_14129 32 64);
      v_14144 <- eval (extract v_14126 64 96);
      v_14146 <- eval (extract v_14129 64 96);
      v_14152 <- eval (extract v_14126 96 128);
      v_14154 <- eval (extract v_14129 96 128);
      setRegister (lhs.of_reg v_3000) (concat (mux (sgt v_14127 (expression.bv_nat 32 0)) v_14130 (mux (eq v_14127 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14130 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14136 (expression.bv_nat 32 0)) v_14138 (mux (eq v_14136 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14138 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14144 (expression.bv_nat 32 0)) v_14146 (mux (eq v_14144 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14146 (expression.bv_nat 32 4294967295))))) (mux (sgt v_14152 (expression.bv_nat 32 0)) v_14154 (mux (eq v_14152 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14154 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end
