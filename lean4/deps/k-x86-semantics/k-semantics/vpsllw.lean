def vpsllw : instruction :=
  definst "vpsllw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- eval (concat (expression.bv_nat 8 0) v_3);
      (v_7 : expression (bv 16)) <- eval (extract (shl v_5 v_6) 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_9 : expression (bv 16)) <- eval (extract (shl v_8 v_6) 0 16);
      (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_6) 0 16);
      (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_6) 0 16);
      (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_6) 0 16);
      (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_6) 0 16);
      (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_6) 0 16);
      (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_6) 0 16);
      setRegister (lhs.of_reg xmm_2) (mux (ugt (concat (expression.bv_nat 56 0) v_3) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat v_7 (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 v_21))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- eval (concat (expression.bv_nat 8 0) v_3);
      (v_7 : expression (bv 16)) <- eval (extract (shl v_5 v_6) 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_9 : expression (bv 16)) <- eval (extract (shl v_8 v_6) 0 16);
      (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_6) 0 16);
      (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_6) 0 16);
      (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_6) 0 16);
      (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_6) 0 16);
      (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_6) 0 16);
      (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_6) 0 16);
      (v_22 : expression (bv 16)) <- eval (extract v_4 128 144);
      (v_23 : expression (bv 16)) <- eval (extract (shl v_22 v_6) 0 16);
      (v_24 : expression (bv 16)) <- eval (extract v_4 144 160);
      (v_25 : expression (bv 16)) <- eval (extract (shl v_24 v_6) 0 16);
      (v_26 : expression (bv 16)) <- eval (extract v_4 160 176);
      (v_27 : expression (bv 16)) <- eval (extract (shl v_26 v_6) 0 16);
      (v_28 : expression (bv 16)) <- eval (extract v_4 176 192);
      (v_29 : expression (bv 16)) <- eval (extract (shl v_28 v_6) 0 16);
      (v_30 : expression (bv 16)) <- eval (extract v_4 192 208);
      (v_31 : expression (bv 16)) <- eval (extract (shl v_30 v_6) 0 16);
      (v_32 : expression (bv 16)) <- eval (extract v_4 208 224);
      (v_33 : expression (bv 16)) <- eval (extract (shl v_32 v_6) 0 16);
      (v_34 : expression (bv 16)) <- eval (extract v_4 224 240);
      (v_35 : expression (bv 16)) <- eval (extract (shl v_34 v_6) 0 16);
      (v_36 : expression (bv 16)) <- eval (extract v_4 240 256);
      (v_37 : expression (bv 16)) <- eval (extract (shl v_36 v_6) 0 16);
      setRegister (lhs.of_reg ymm_2) (mux (ugt (concat (expression.bv_nat 56 0) v_3) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat v_7 (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 (concat v_21 (concat v_23 (concat v_25 (concat v_27 (concat v_29 (concat v_31 (concat v_33 (concat v_35 v_37))))))))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_9 : expression (bv 16)) <- eval (extract (shl v_7 v_8) 0 16);
      (v_10 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_8) 0 16);
      (v_12 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_8) 0 16);
      (v_14 : expression (bv 16)) <- eval (extract v_6 48 64);
      (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_8) 0 16);
      (v_16 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_8) 0 16);
      (v_18 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_8) 0 16);
      (v_20 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_8) 0 16);
      (v_22 : expression (bv 16)) <- eval (extract v_6 112 128);
      (v_23 : expression (bv 16)) <- eval (extract (shl v_22 v_8) 0 16);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 (concat v_21 v_23))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_9 : expression (bv 16)) <- eval (extract (shl v_7 v_8) 0 16);
      (v_10 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_8) 0 16);
      (v_12 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_8) 0 16);
      (v_14 : expression (bv 16)) <- eval (extract v_6 48 64);
      (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_8) 0 16);
      (v_16 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_8) 0 16);
      (v_18 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_8) 0 16);
      (v_20 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_8) 0 16);
      (v_22 : expression (bv 16)) <- eval (extract v_6 112 128);
      (v_23 : expression (bv 16)) <- eval (extract (shl v_22 v_8) 0 16);
      (v_24 : expression (bv 16)) <- eval (extract v_6 128 144);
      (v_25 : expression (bv 16)) <- eval (extract (shl v_24 v_8) 0 16);
      (v_26 : expression (bv 16)) <- eval (extract v_6 144 160);
      (v_27 : expression (bv 16)) <- eval (extract (shl v_26 v_8) 0 16);
      (v_28 : expression (bv 16)) <- eval (extract v_6 160 176);
      (v_29 : expression (bv 16)) <- eval (extract (shl v_28 v_8) 0 16);
      (v_30 : expression (bv 16)) <- eval (extract v_6 176 192);
      (v_31 : expression (bv 16)) <- eval (extract (shl v_30 v_8) 0 16);
      (v_32 : expression (bv 16)) <- eval (extract v_6 192 208);
      (v_33 : expression (bv 16)) <- eval (extract (shl v_32 v_8) 0 16);
      (v_34 : expression (bv 16)) <- eval (extract v_6 208 224);
      (v_35 : expression (bv 16)) <- eval (extract (shl v_34 v_8) 0 16);
      (v_36 : expression (bv 16)) <- eval (extract v_6 224 240);
      (v_37 : expression (bv 16)) <- eval (extract (shl v_36 v_8) 0 16);
      (v_38 : expression (bv 16)) <- eval (extract v_6 240 256);
      (v_39 : expression (bv 16)) <- eval (extract (shl v_38 v_8) 0 16);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 (concat v_21 (concat v_23 (concat v_25 (concat v_27 (concat v_29 (concat v_31 (concat v_33 (concat v_35 (concat v_37 v_39))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat v_8 (concat v_10 (concat v_12 (concat v_14 (concat v_16 (concat v_18 (concat v_20 v_22))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      (v_23 : expression (bv 16)) <- eval (extract v_5 128 144);
      (v_24 : expression (bv 16)) <- eval (extract (shl v_23 v_7) 0 16);
      (v_25 : expression (bv 16)) <- eval (extract v_5 144 160);
      (v_26 : expression (bv 16)) <- eval (extract (shl v_25 v_7) 0 16);
      (v_27 : expression (bv 16)) <- eval (extract v_5 160 176);
      (v_28 : expression (bv 16)) <- eval (extract (shl v_27 v_7) 0 16);
      (v_29 : expression (bv 16)) <- eval (extract v_5 176 192);
      (v_30 : expression (bv 16)) <- eval (extract (shl v_29 v_7) 0 16);
      (v_31 : expression (bv 16)) <- eval (extract v_5 192 208);
      (v_32 : expression (bv 16)) <- eval (extract (shl v_31 v_7) 0 16);
      (v_33 : expression (bv 16)) <- eval (extract v_5 208 224);
      (v_34 : expression (bv 16)) <- eval (extract (shl v_33 v_7) 0 16);
      (v_35 : expression (bv 16)) <- eval (extract v_5 224 240);
      (v_36 : expression (bv 16)) <- eval (extract (shl v_35 v_7) 0 16);
      (v_37 : expression (bv 16)) <- eval (extract v_5 240 256);
      (v_38 : expression (bv 16)) <- eval (extract (shl v_37 v_7) 0 16);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat v_8 (concat v_10 (concat v_12 (concat v_14 (concat v_16 (concat v_18 (concat v_20 (concat v_22 (concat v_24 (concat v_26 (concat v_28 (concat v_30 (concat v_32 (concat v_34 (concat v_36 v_38))))))))))))))));
      pure ()
    pat_end
