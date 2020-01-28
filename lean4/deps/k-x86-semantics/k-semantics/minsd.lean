def minsd : instruction :=
  definst "minsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (extract v_2 64 128);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (mux (eq (/- (_,_) -/  mincmp_double v_3 v_5) (expression.bv_nat 1 1)) v_3 v_5));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (extract v_2 64 128);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (extract v_4 64 128);
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (mux (eq (/- (_,_) -/  mincmp_double v_3 v_5) (expression.bv_nat 1 1)) v_3 v_5));
      pure ()
    pat_end
