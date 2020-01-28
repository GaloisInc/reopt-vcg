def vmaxsd : instruction :=
  definst "vmaxsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (extract v_3 64 128);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 8;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (mux (eq (/- (_,_) -/  maxcmp_double v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      v_6 <- eval (extract v_5 64 128);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (mux (eq (/- (_,_) -/  maxcmp_double v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6));
      pure ()
    pat_end
