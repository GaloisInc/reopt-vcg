def vminss : instruction :=
  definst "vminss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (extract v_3 96 128);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 4;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (mux (eq (/- (_,_) -/  mincmp_single v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (extract v_3 96 128);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      v_6 <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (mux (eq (/- (_,_) -/  mincmp_single v_4 v_6) (expression.bv_nat 1 1)) v_4 v_6));
      pure ()
    pat_end
