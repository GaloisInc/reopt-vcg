def vcvtps2ph : instruction :=
  definst "vcvtps2ph" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      v_7 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      store v_3 (concat (fp_bitcast_to_bv (Float2Half v_6 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_9 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_11 v_7) 16) (fp_bitcast_to_bv (Float2Half v_13 v_7) 16)))) 8;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      v_6 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      setRegister (lhs.of_reg xmm_2) (concat (expression.bv_nat 64 0) (concat (fp_bitcast_to_bv (Float2Half v_5 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_8 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_10 v_6) 16) (fp_bitcast_to_bv (Float2Half v_12 v_6) 16)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg ymm_1);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      v_7 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      (v_14 : expression (bv 32)) <- eval (extract v_4 128 160);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      (v_16 : expression (bv 32)) <- eval (extract v_4 160 192);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      (v_18 : expression (bv 32)) <- eval (extract v_4 192 224);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      (v_20 : expression (bv 32)) <- eval (extract v_4 224 256);
      v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      store v_3 (concat (fp_bitcast_to_bv (Float2Half v_6 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_9 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_11 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_13 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_15 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_17 v_7) 16) (concat (fp_bitcast_to_bv (Float2Half v_19 v_7) 16) (fp_bitcast_to_bv (Float2Half v_21 v_7) 16)))))))) 16;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      v_6 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      (v_13 : expression (bv 32)) <- eval (extract v_3 128 160);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      (v_15 : expression (bv 32)) <- eval (extract v_3 160 192);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      (v_17 : expression (bv 32)) <- eval (extract v_3 192 224);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      (v_19 : expression (bv 32)) <- eval (extract v_3 224 256);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (Float2Half v_5 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_8 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_10 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_12 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_14 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_16 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_18 v_6) 16) (fp_bitcast_to_bv (Float2Half v_20 v_6) 16))))))));
      pure ()
    pat_end
