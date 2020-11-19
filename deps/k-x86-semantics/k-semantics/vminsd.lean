def vminsd : instruction :=
  definst "vminsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 8;
      setRegister (lhs.of_reg xmm_2) (concat v_4 (mux (eq (/- (_,_) -/  mincmp_double v_5 v_7) (expression.bv_nat 1 1)) v_5 v_7));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_6 <- getRegister (lhs.of_reg xmm_0);
      (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (mux (eq (/- (_,_) -/  mincmp_double v_5 v_7) (expression.bv_nat 1 1)) v_5 v_7));
      pure ()
    pat_end
