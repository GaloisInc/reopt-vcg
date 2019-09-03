def vpsllw1 : instruction :=
  definst "vpsllw" $ do
    pattern fun (v_3169 : imm int) (v_3171 : reg (bv 128)) (v_3172 : reg (bv 128)) => do
      v_7979 <- eval (handleImmediateWithSignExtend v_3169 8 8);
      v_7982 <- getRegister v_3171;
      v_7985 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_7979));
      setRegister (lhs.of_reg v_3172) (mux (ugt (concat (expression.bv_nat 56 0) v_7979) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7982 0 16) v_7985) 0 16) (concat (extract (shl (extract v_7982 16 32) v_7985) 0 16) (concat (extract (shl (extract v_7982 32 48) v_7985) 0 16) (concat (extract (shl (extract v_7982 48 64) v_7985) 0 16) (concat (extract (shl (extract v_7982 64 80) v_7985) 0 16) (concat (extract (shl (extract v_7982 80 96) v_7985) 0 16) (concat (extract (shl (extract v_7982 96 112) v_7985) 0 16) (extract (shl (extract v_7982 112 128) v_7985) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3181 : reg (bv 128)) (v_3182 : reg (bv 128)) (v_3183 : reg (bv 128)) => do
      v_8023 <- getRegister v_3181;
      v_8026 <- getRegister v_3182;
      v_8029 <- eval (uvalueMInt (extract v_8023 112 128));
      setRegister (lhs.of_reg v_3183) (mux (ugt (extract v_8023 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_8026 0 16) v_8029) 0 16) (concat (extract (shl (extract v_8026 16 32) v_8029) 0 16) (concat (extract (shl (extract v_8026 32 48) v_8029) 0 16) (concat (extract (shl (extract v_8026 48 64) v_8029) 0 16) (concat (extract (shl (extract v_8026 64 80) v_8029) 0 16) (concat (extract (shl (extract v_8026 80 96) v_8029) 0 16) (concat (extract (shl (extract v_8026 96 112) v_8029) 0 16) (extract (shl (extract v_8026 112 128) v_8029) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3186 : imm int) (v_3189 : reg (bv 256)) (v_3190 : reg (bv 256)) => do
      v_8062 <- eval (handleImmediateWithSignExtend v_3186 8 8);
      v_8065 <- getRegister v_3189;
      v_8068 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_8062));
      setRegister (lhs.of_reg v_3190) (mux (ugt (concat (expression.bv_nat 56 0) v_8062) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_8065 0 16) v_8068) 0 16) (concat (extract (shl (extract v_8065 16 32) v_8068) 0 16) (concat (extract (shl (extract v_8065 32 48) v_8068) 0 16) (concat (extract (shl (extract v_8065 48 64) v_8068) 0 16) (concat (extract (shl (extract v_8065 64 80) v_8068) 0 16) (concat (extract (shl (extract v_8065 80 96) v_8068) 0 16) (concat (extract (shl (extract v_8065 96 112) v_8068) 0 16) (concat (extract (shl (extract v_8065 112 128) v_8068) 0 16) (concat (extract (shl (extract v_8065 128 144) v_8068) 0 16) (concat (extract (shl (extract v_8065 144 160) v_8068) 0 16) (concat (extract (shl (extract v_8065 160 176) v_8068) 0 16) (concat (extract (shl (extract v_8065 176 192) v_8068) 0 16) (concat (extract (shl (extract v_8065 192 208) v_8068) 0 16) (concat (extract (shl (extract v_8065 208 224) v_8068) 0 16) (concat (extract (shl (extract v_8065 224 240) v_8068) 0 16) (extract (shl (extract v_8065 240 256) v_8068) 0 16)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3198 : reg (bv 128)) (v_3200 : reg (bv 256)) (v_3201 : reg (bv 256)) => do
      v_8138 <- getRegister v_3198;
      v_8141 <- getRegister v_3200;
      v_8144 <- eval (uvalueMInt (extract v_8138 112 128));
      setRegister (lhs.of_reg v_3201) (mux (ugt (extract v_8138 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_8141 0 16) v_8144) 0 16) (concat (extract (shl (extract v_8141 16 32) v_8144) 0 16) (concat (extract (shl (extract v_8141 32 48) v_8144) 0 16) (concat (extract (shl (extract v_8141 48 64) v_8144) 0 16) (concat (extract (shl (extract v_8141 64 80) v_8144) 0 16) (concat (extract (shl (extract v_8141 80 96) v_8144) 0 16) (concat (extract (shl (extract v_8141 96 112) v_8144) 0 16) (concat (extract (shl (extract v_8141 112 128) v_8144) 0 16) (concat (extract (shl (extract v_8141 128 144) v_8144) 0 16) (concat (extract (shl (extract v_8141 144 160) v_8144) 0 16) (concat (extract (shl (extract v_8141 160 176) v_8144) 0 16) (concat (extract (shl (extract v_8141 176 192) v_8144) 0 16) (concat (extract (shl (extract v_8141 192 208) v_8144) 0 16) (concat (extract (shl (extract v_8141 208 224) v_8144) 0 16) (concat (extract (shl (extract v_8141 224 240) v_8144) 0 16) (extract (shl (extract v_8141 240 256) v_8144) 0 16)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3175 : Mem) (v_3176 : reg (bv 128)) (v_3177 : reg (bv 128)) => do
      v_14355 <- evaluateAddress v_3175;
      v_14356 <- load v_14355 16;
      v_14359 <- getRegister v_3176;
      v_14362 <- eval (uvalueMInt (extract v_14356 112 128));
      setRegister (lhs.of_reg v_3177) (mux (ugt (extract v_14356 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14359 0 16) v_14362) 0 16) (concat (extract (shl (extract v_14359 16 32) v_14362) 0 16) (concat (extract (shl (extract v_14359 32 48) v_14362) 0 16) (concat (extract (shl (extract v_14359 48 64) v_14362) 0 16) (concat (extract (shl (extract v_14359 64 80) v_14362) 0 16) (concat (extract (shl (extract v_14359 80 96) v_14362) 0 16) (concat (extract (shl (extract v_14359 96 112) v_14362) 0 16) (extract (shl (extract v_14359 112 128) v_14362) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3192 : Mem) (v_3194 : reg (bv 256)) (v_3195 : reg (bv 256)) => do
      v_14395 <- evaluateAddress v_3192;
      v_14396 <- load v_14395 16;
      v_14399 <- getRegister v_3194;
      v_14402 <- eval (uvalueMInt (extract v_14396 112 128));
      setRegister (lhs.of_reg v_3195) (mux (ugt (extract v_14396 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_14399 0 16) v_14402) 0 16) (concat (extract (shl (extract v_14399 16 32) v_14402) 0 16) (concat (extract (shl (extract v_14399 32 48) v_14402) 0 16) (concat (extract (shl (extract v_14399 48 64) v_14402) 0 16) (concat (extract (shl (extract v_14399 64 80) v_14402) 0 16) (concat (extract (shl (extract v_14399 80 96) v_14402) 0 16) (concat (extract (shl (extract v_14399 96 112) v_14402) 0 16) (concat (extract (shl (extract v_14399 112 128) v_14402) 0 16) (concat (extract (shl (extract v_14399 128 144) v_14402) 0 16) (concat (extract (shl (extract v_14399 144 160) v_14402) 0 16) (concat (extract (shl (extract v_14399 160 176) v_14402) 0 16) (concat (extract (shl (extract v_14399 176 192) v_14402) 0 16) (concat (extract (shl (extract v_14399 192 208) v_14402) 0 16) (concat (extract (shl (extract v_14399 208 224) v_14402) 0 16) (concat (extract (shl (extract v_14399 224 240) v_14402) 0 16) (extract (shl (extract v_14399 240 256) v_14402) 0 16)))))))))))))))));
      pure ()
    pat_end
