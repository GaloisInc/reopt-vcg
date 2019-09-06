def vpsllw1 : instruction :=
  definst "vpsllw" $ do
    pattern fun (v_3249 : imm int) (v_3251 : reg (bv 128)) (v_3252 : reg (bv 128)) => do
      v_8027 <- eval (handleImmediateWithSignExtend v_3249 8 8);
      v_8030 <- getRegister v_3251;
      v_8032 <- eval (concat (expression.bv_nat 8 0) v_8027);
      setRegister (lhs.of_reg v_3252) (mux (ugt (concat (expression.bv_nat 56 0) v_8027) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_8030 0 16) v_8032) 0 16) (concat (extract (shl (extract v_8030 16 32) v_8032) 0 16) (concat (extract (shl (extract v_8030 32 48) v_8032) 0 16) (concat (extract (shl (extract v_8030 48 64) v_8032) 0 16) (concat (extract (shl (extract v_8030 64 80) v_8032) 0 16) (concat (extract (shl (extract v_8030 80 96) v_8032) 0 16) (concat (extract (shl (extract v_8030 96 112) v_8032) 0 16) (extract (shl (extract v_8030 112 128) v_8032) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3261 : reg (bv 128)) (v_3262 : reg (bv 128)) (v_3263 : reg (bv 128)) => do
      v_8070 <- getRegister v_3261;
      v_8073 <- getRegister v_3262;
      v_8075 <- eval (extract v_8070 112 128);
      setRegister (lhs.of_reg v_3263) (mux (ugt (extract v_8070 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_8073 0 16) v_8075) 0 16) (concat (extract (shl (extract v_8073 16 32) v_8075) 0 16) (concat (extract (shl (extract v_8073 32 48) v_8075) 0 16) (concat (extract (shl (extract v_8073 48 64) v_8075) 0 16) (concat (extract (shl (extract v_8073 64 80) v_8075) 0 16) (concat (extract (shl (extract v_8073 80 96) v_8075) 0 16) (concat (extract (shl (extract v_8073 96 112) v_8075) 0 16) (extract (shl (extract v_8073 112 128) v_8075) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3266 : imm int) (v_3268 : reg (bv 256)) (v_3269 : reg (bv 256)) => do
      v_8108 <- eval (handleImmediateWithSignExtend v_3266 8 8);
      v_8111 <- getRegister v_3268;
      v_8113 <- eval (concat (expression.bv_nat 8 0) v_8108);
      setRegister (lhs.of_reg v_3269) (mux (ugt (concat (expression.bv_nat 56 0) v_8108) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_8111 0 16) v_8113) 0 16) (concat (extract (shl (extract v_8111 16 32) v_8113) 0 16) (concat (extract (shl (extract v_8111 32 48) v_8113) 0 16) (concat (extract (shl (extract v_8111 48 64) v_8113) 0 16) (concat (extract (shl (extract v_8111 64 80) v_8113) 0 16) (concat (extract (shl (extract v_8111 80 96) v_8113) 0 16) (concat (extract (shl (extract v_8111 96 112) v_8113) 0 16) (concat (extract (shl (extract v_8111 112 128) v_8113) 0 16) (concat (extract (shl (extract v_8111 128 144) v_8113) 0 16) (concat (extract (shl (extract v_8111 144 160) v_8113) 0 16) (concat (extract (shl (extract v_8111 160 176) v_8113) 0 16) (concat (extract (shl (extract v_8111 176 192) v_8113) 0 16) (concat (extract (shl (extract v_8111 192 208) v_8113) 0 16) (concat (extract (shl (extract v_8111 208 224) v_8113) 0 16) (concat (extract (shl (extract v_8111 224 240) v_8113) 0 16) (extract (shl (extract v_8111 240 256) v_8113) 0 16)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3280 : reg (bv 128)) (v_3278 : reg (bv 256)) (v_3279 : reg (bv 256)) => do
      v_8183 <- getRegister v_3280;
      v_8186 <- getRegister v_3278;
      v_8188 <- eval (extract v_8183 112 128);
      setRegister (lhs.of_reg v_3279) (mux (ugt (extract v_8183 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_8186 0 16) v_8188) 0 16) (concat (extract (shl (extract v_8186 16 32) v_8188) 0 16) (concat (extract (shl (extract v_8186 32 48) v_8188) 0 16) (concat (extract (shl (extract v_8186 48 64) v_8188) 0 16) (concat (extract (shl (extract v_8186 64 80) v_8188) 0 16) (concat (extract (shl (extract v_8186 80 96) v_8188) 0 16) (concat (extract (shl (extract v_8186 96 112) v_8188) 0 16) (concat (extract (shl (extract v_8186 112 128) v_8188) 0 16) (concat (extract (shl (extract v_8186 128 144) v_8188) 0 16) (concat (extract (shl (extract v_8186 144 160) v_8188) 0 16) (concat (extract (shl (extract v_8186 160 176) v_8188) 0 16) (concat (extract (shl (extract v_8186 176 192) v_8188) 0 16) (concat (extract (shl (extract v_8186 192 208) v_8188) 0 16) (concat (extract (shl (extract v_8186 208 224) v_8188) 0 16) (concat (extract (shl (extract v_8186 224 240) v_8188) 0 16) (extract (shl (extract v_8186 240 256) v_8188) 0 16)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3255 : Mem) (v_3256 : reg (bv 128)) (v_3257 : reg (bv 128)) => do
      v_14155 <- evaluateAddress v_3255;
      v_14156 <- load v_14155 16;
      v_14159 <- getRegister v_3256;
      v_14161 <- eval (extract v_14156 112 128);
      setRegister (lhs.of_reg v_3257) (mux (ugt (extract v_14156 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14159 0 16) v_14161) 0 16) (concat (extract (shl (extract v_14159 16 32) v_14161) 0 16) (concat (extract (shl (extract v_14159 32 48) v_14161) 0 16) (concat (extract (shl (extract v_14159 48 64) v_14161) 0 16) (concat (extract (shl (extract v_14159 64 80) v_14161) 0 16) (concat (extract (shl (extract v_14159 80 96) v_14161) 0 16) (concat (extract (shl (extract v_14159 96 112) v_14161) 0 16) (extract (shl (extract v_14159 112 128) v_14161) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3272 : Mem) (v_3273 : reg (bv 256)) (v_3274 : reg (bv 256)) => do
      v_14194 <- evaluateAddress v_3272;
      v_14195 <- load v_14194 16;
      v_14198 <- getRegister v_3273;
      v_14200 <- eval (extract v_14195 112 128);
      setRegister (lhs.of_reg v_3274) (mux (ugt (extract v_14195 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_14198 0 16) v_14200) 0 16) (concat (extract (shl (extract v_14198 16 32) v_14200) 0 16) (concat (extract (shl (extract v_14198 32 48) v_14200) 0 16) (concat (extract (shl (extract v_14198 48 64) v_14200) 0 16) (concat (extract (shl (extract v_14198 64 80) v_14200) 0 16) (concat (extract (shl (extract v_14198 80 96) v_14200) 0 16) (concat (extract (shl (extract v_14198 96 112) v_14200) 0 16) (concat (extract (shl (extract v_14198 112 128) v_14200) 0 16) (concat (extract (shl (extract v_14198 128 144) v_14200) 0 16) (concat (extract (shl (extract v_14198 144 160) v_14200) 0 16) (concat (extract (shl (extract v_14198 160 176) v_14200) 0 16) (concat (extract (shl (extract v_14198 176 192) v_14200) 0 16) (concat (extract (shl (extract v_14198 192 208) v_14200) 0 16) (concat (extract (shl (extract v_14198 208 224) v_14200) 0 16) (concat (extract (shl (extract v_14198 224 240) v_14200) 0 16) (extract (shl (extract v_14198 240 256) v_14200) 0 16)))))))))))))))));
      pure ()
    pat_end
