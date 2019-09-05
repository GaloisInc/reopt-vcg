def vpsllw1 : instruction :=
  definst "vpsllw" $ do
    pattern fun (v_3220 : imm int) (v_3224 : reg (bv 128)) (v_3225 : reg (bv 128)) => do
      v_8000 <- eval (handleImmediateWithSignExtend v_3220 8 8);
      v_8003 <- getRegister v_3224;
      v_8005 <- eval (concat (expression.bv_nat 8 0) v_8000);
      setRegister (lhs.of_reg v_3225) (mux (ugt (concat (expression.bv_nat 56 0) v_8000) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_8003 0 16) v_8005) 0 16) (concat (extract (shl (extract v_8003 16 32) v_8005) 0 16) (concat (extract (shl (extract v_8003 32 48) v_8005) 0 16) (concat (extract (shl (extract v_8003 48 64) v_8005) 0 16) (concat (extract (shl (extract v_8003 64 80) v_8005) 0 16) (concat (extract (shl (extract v_8003 80 96) v_8005) 0 16) (concat (extract (shl (extract v_8003 96 112) v_8005) 0 16) (extract (shl (extract v_8003 112 128) v_8005) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3234 : reg (bv 128)) (v_3235 : reg (bv 128)) (v_3236 : reg (bv 128)) => do
      v_8043 <- getRegister v_3234;
      v_8046 <- getRegister v_3235;
      v_8048 <- eval (extract v_8043 112 128);
      setRegister (lhs.of_reg v_3236) (mux (ugt (extract v_8043 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_8046 0 16) v_8048) 0 16) (concat (extract (shl (extract v_8046 16 32) v_8048) 0 16) (concat (extract (shl (extract v_8046 32 48) v_8048) 0 16) (concat (extract (shl (extract v_8046 48 64) v_8048) 0 16) (concat (extract (shl (extract v_8046 64 80) v_8048) 0 16) (concat (extract (shl (extract v_8046 80 96) v_8048) 0 16) (concat (extract (shl (extract v_8046 96 112) v_8048) 0 16) (extract (shl (extract v_8046 112 128) v_8048) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3237 : imm int) (v_3241 : reg (bv 256)) (v_3242 : reg (bv 256)) => do
      v_8081 <- eval (handleImmediateWithSignExtend v_3237 8 8);
      v_8084 <- getRegister v_3241;
      v_8086 <- eval (concat (expression.bv_nat 8 0) v_8081);
      setRegister (lhs.of_reg v_3242) (mux (ugt (concat (expression.bv_nat 56 0) v_8081) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_8084 0 16) v_8086) 0 16) (concat (extract (shl (extract v_8084 16 32) v_8086) 0 16) (concat (extract (shl (extract v_8084 32 48) v_8086) 0 16) (concat (extract (shl (extract v_8084 48 64) v_8086) 0 16) (concat (extract (shl (extract v_8084 64 80) v_8086) 0 16) (concat (extract (shl (extract v_8084 80 96) v_8086) 0 16) (concat (extract (shl (extract v_8084 96 112) v_8086) 0 16) (concat (extract (shl (extract v_8084 112 128) v_8086) 0 16) (concat (extract (shl (extract v_8084 128 144) v_8086) 0 16) (concat (extract (shl (extract v_8084 144 160) v_8086) 0 16) (concat (extract (shl (extract v_8084 160 176) v_8086) 0 16) (concat (extract (shl (extract v_8084 176 192) v_8086) 0 16) (concat (extract (shl (extract v_8084 192 208) v_8086) 0 16) (concat (extract (shl (extract v_8084 208 224) v_8086) 0 16) (concat (extract (shl (extract v_8084 224 240) v_8086) 0 16) (extract (shl (extract v_8084 240 256) v_8086) 0 16)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3253 : reg (bv 128)) (v_3251 : reg (bv 256)) (v_3252 : reg (bv 256)) => do
      v_8156 <- getRegister v_3253;
      v_8159 <- getRegister v_3251;
      v_8161 <- eval (extract v_8156 112 128);
      setRegister (lhs.of_reg v_3252) (mux (ugt (extract v_8156 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_8159 0 16) v_8161) 0 16) (concat (extract (shl (extract v_8159 16 32) v_8161) 0 16) (concat (extract (shl (extract v_8159 32 48) v_8161) 0 16) (concat (extract (shl (extract v_8159 48 64) v_8161) 0 16) (concat (extract (shl (extract v_8159 64 80) v_8161) 0 16) (concat (extract (shl (extract v_8159 80 96) v_8161) 0 16) (concat (extract (shl (extract v_8159 96 112) v_8161) 0 16) (concat (extract (shl (extract v_8159 112 128) v_8161) 0 16) (concat (extract (shl (extract v_8159 128 144) v_8161) 0 16) (concat (extract (shl (extract v_8159 144 160) v_8161) 0 16) (concat (extract (shl (extract v_8159 160 176) v_8161) 0 16) (concat (extract (shl (extract v_8159 176 192) v_8161) 0 16) (concat (extract (shl (extract v_8159 192 208) v_8161) 0 16) (concat (extract (shl (extract v_8159 208 224) v_8161) 0 16) (concat (extract (shl (extract v_8159 224 240) v_8161) 0 16) (extract (shl (extract v_8159 240 256) v_8161) 0 16)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3228 : Mem) (v_3229 : reg (bv 128)) (v_3230 : reg (bv 128)) => do
      v_14128 <- evaluateAddress v_3228;
      v_14129 <- load v_14128 16;
      v_14132 <- getRegister v_3229;
      v_14134 <- eval (extract v_14129 112 128);
      setRegister (lhs.of_reg v_3230) (mux (ugt (extract v_14129 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14132 0 16) v_14134) 0 16) (concat (extract (shl (extract v_14132 16 32) v_14134) 0 16) (concat (extract (shl (extract v_14132 32 48) v_14134) 0 16) (concat (extract (shl (extract v_14132 48 64) v_14134) 0 16) (concat (extract (shl (extract v_14132 64 80) v_14134) 0 16) (concat (extract (shl (extract v_14132 80 96) v_14134) 0 16) (concat (extract (shl (extract v_14132 96 112) v_14134) 0 16) (extract (shl (extract v_14132 112 128) v_14134) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3245 : Mem) (v_3246 : reg (bv 256)) (v_3247 : reg (bv 256)) => do
      v_14167 <- evaluateAddress v_3245;
      v_14168 <- load v_14167 16;
      v_14171 <- getRegister v_3246;
      v_14173 <- eval (extract v_14168 112 128);
      setRegister (lhs.of_reg v_3247) (mux (ugt (extract v_14168 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_14171 0 16) v_14173) 0 16) (concat (extract (shl (extract v_14171 16 32) v_14173) 0 16) (concat (extract (shl (extract v_14171 32 48) v_14173) 0 16) (concat (extract (shl (extract v_14171 48 64) v_14173) 0 16) (concat (extract (shl (extract v_14171 64 80) v_14173) 0 16) (concat (extract (shl (extract v_14171 80 96) v_14173) 0 16) (concat (extract (shl (extract v_14171 96 112) v_14173) 0 16) (concat (extract (shl (extract v_14171 112 128) v_14173) 0 16) (concat (extract (shl (extract v_14171 128 144) v_14173) 0 16) (concat (extract (shl (extract v_14171 144 160) v_14173) 0 16) (concat (extract (shl (extract v_14171 160 176) v_14173) 0 16) (concat (extract (shl (extract v_14171 176 192) v_14173) 0 16) (concat (extract (shl (extract v_14171 192 208) v_14173) 0 16) (concat (extract (shl (extract v_14171 208 224) v_14173) 0 16) (concat (extract (shl (extract v_14171 224 240) v_14173) 0 16) (extract (shl (extract v_14171 240 256) v_14173) 0 16)))))))))))))))));
      pure ()
    pat_end
