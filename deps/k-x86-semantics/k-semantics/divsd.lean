def divsd : instruction :=
  definst "divsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      (v_4 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 8;
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (fp_bitcast_to_bv (fp_div v_5 v_8) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      (v_4 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg xmm_0);
      (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (fp_bitcast_to_bv (fp_div v_5 v_8) 64));
      pure ()
    pat_end
