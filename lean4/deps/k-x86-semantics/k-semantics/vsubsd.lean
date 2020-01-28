def vsubsd : instruction :=
  definst "vsubsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 8;
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (fp_bitcast_to_bv (fp_sub v_4 v_7) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_5 <- getRegister (lhs.of_reg xmm_0);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (fp_bitcast_to_bv (fp_sub v_4 v_6) 64));
      pure ()
    pat_end
