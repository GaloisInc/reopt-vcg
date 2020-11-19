def minss : instruction :=
  definst "minss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 4;
      setRegister (lhs.of_reg xmm_1) (concat v_3 (mux (eq (/- (_,_) -/  mincmp_single v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (mux (eq (/- (_,_) -/  mincmp_single v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6));
      pure ()
    pat_end
