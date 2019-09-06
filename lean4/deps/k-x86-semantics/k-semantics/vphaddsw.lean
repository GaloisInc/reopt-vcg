def vphaddsw1 : instruction :=
  definst "vphaddsw" $ do
    pattern fun (v_3262 : reg (bv 128)) (v_3263 : reg (bv 128)) (v_3264 : reg (bv 128)) => do
      v_8752 <- getRegister v_3262;
      v_8757 <- eval (add (sext (extract v_8752 0 16) 32) (sext (extract v_8752 16 32) 32));
      v_8767 <- eval (add (sext (extract v_8752 32 48) 32) (sext (extract v_8752 48 64) 32));
      v_8777 <- eval (add (sext (extract v_8752 64 80) 32) (sext (extract v_8752 80 96) 32));
      v_8787 <- eval (add (sext (extract v_8752 96 112) 32) (sext (extract v_8752 112 128) 32));
      v_8793 <- getRegister v_3263;
      v_8798 <- eval (add (sext (extract v_8793 0 16) 32) (sext (extract v_8793 16 32) 32));
      v_8808 <- eval (add (sext (extract v_8793 32 48) 32) (sext (extract v_8793 48 64) 32));
      v_8818 <- eval (add (sext (extract v_8793 64 80) 32) (sext (extract v_8793 80 96) 32));
      v_8828 <- eval (add (sext (extract v_8793 112 128) 32) (sext (extract v_8793 96 112) 32));
      setRegister (lhs.of_reg v_3264) (concat (mux (sgt v_8757 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8757 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8757 16 32))) (concat (mux (sgt v_8767 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8767 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8767 16 32))) (concat (mux (sgt v_8777 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8777 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8777 16 32))) (concat (mux (sgt v_8787 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8787 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8787 16 32))) (concat (mux (sgt v_8798 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8798 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8798 16 32))) (concat (mux (sgt v_8808 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8808 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8808 16 32))) (concat (mux (sgt v_8818 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8818 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8818 16 32))) (mux (sgt v_8828 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8828 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8828 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3273 : reg (bv 256)) (v_3274 : reg (bv 256)) (v_3275 : reg (bv 256)) => do
      v_8847 <- getRegister v_3273;
      v_8852 <- eval (add (sext (extract v_8847 0 16) 32) (sext (extract v_8847 16 32) 32));
      v_8862 <- eval (add (sext (extract v_8847 32 48) 32) (sext (extract v_8847 48 64) 32));
      v_8872 <- eval (add (sext (extract v_8847 64 80) 32) (sext (extract v_8847 80 96) 32));
      v_8882 <- eval (add (sext (extract v_8847 96 112) 32) (sext (extract v_8847 112 128) 32));
      v_8888 <- getRegister v_3274;
      v_8893 <- eval (add (sext (extract v_8888 0 16) 32) (sext (extract v_8888 16 32) 32));
      v_8903 <- eval (add (sext (extract v_8888 32 48) 32) (sext (extract v_8888 48 64) 32));
      v_8913 <- eval (add (sext (extract v_8888 64 80) 32) (sext (extract v_8888 80 96) 32));
      v_8923 <- eval (add (sext (extract v_8888 96 112) 32) (sext (extract v_8888 112 128) 32));
      v_8933 <- eval (add (sext (extract v_8847 128 144) 32) (sext (extract v_8847 144 160) 32));
      v_8943 <- eval (add (sext (extract v_8847 160 176) 32) (sext (extract v_8847 176 192) 32));
      v_8953 <- eval (add (sext (extract v_8847 192 208) 32) (sext (extract v_8847 208 224) 32));
      v_8963 <- eval (add (sext (extract v_8847 224 240) 32) (sext (extract v_8847 240 256) 32));
      v_8973 <- eval (add (sext (extract v_8888 128 144) 32) (sext (extract v_8888 144 160) 32));
      v_8983 <- eval (add (sext (extract v_8888 160 176) 32) (sext (extract v_8888 176 192) 32));
      v_8993 <- eval (add (sext (extract v_8888 192 208) 32) (sext (extract v_8888 208 224) 32));
      v_9003 <- eval (add (sext (extract v_8888 240 256) 32) (sext (extract v_8888 224 240) 32));
      setRegister (lhs.of_reg v_3275) (concat (mux (sgt v_8852 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8852 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8852 16 32))) (concat (mux (sgt v_8862 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8862 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8862 16 32))) (concat (mux (sgt v_8872 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8872 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8872 16 32))) (concat (mux (sgt v_8882 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8882 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8882 16 32))) (concat (mux (sgt v_8893 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8893 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8893 16 32))) (concat (mux (sgt v_8903 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8903 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8903 16 32))) (concat (mux (sgt v_8913 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8913 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8913 16 32))) (concat (mux (sgt v_8923 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8923 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8923 16 32))) (concat (mux (sgt v_8933 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8933 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8933 16 32))) (concat (mux (sgt v_8943 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8943 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8943 16 32))) (concat (mux (sgt v_8953 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8953 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8953 16 32))) (concat (mux (sgt v_8963 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8963 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8963 16 32))) (concat (mux (sgt v_8973 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8973 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8973 16 32))) (concat (mux (sgt v_8983 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8983 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8983 16 32))) (concat (mux (sgt v_8993 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8993 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8993 16 32))) (mux (sgt v_9003 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9003 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9003 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3257 : Mem) (v_3258 : reg (bv 128)) (v_3259 : reg (bv 128)) => do
      v_17164 <- evaluateAddress v_3257;
      v_17165 <- load v_17164 16;
      v_17170 <- eval (add (sext (extract v_17165 0 16) 32) (sext (extract v_17165 16 32) 32));
      v_17180 <- eval (add (sext (extract v_17165 32 48) 32) (sext (extract v_17165 48 64) 32));
      v_17190 <- eval (add (sext (extract v_17165 64 80) 32) (sext (extract v_17165 80 96) 32));
      v_17200 <- eval (add (sext (extract v_17165 96 112) 32) (sext (extract v_17165 112 128) 32));
      v_17206 <- getRegister v_3258;
      v_17211 <- eval (add (sext (extract v_17206 0 16) 32) (sext (extract v_17206 16 32) 32));
      v_17221 <- eval (add (sext (extract v_17206 32 48) 32) (sext (extract v_17206 48 64) 32));
      v_17231 <- eval (add (sext (extract v_17206 64 80) 32) (sext (extract v_17206 80 96) 32));
      v_17241 <- eval (add (sext (extract v_17206 112 128) 32) (sext (extract v_17206 96 112) 32));
      setRegister (lhs.of_reg v_3259) (concat (mux (sgt v_17170 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17170 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17170 16 32))) (concat (mux (sgt v_17180 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17180 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17180 16 32))) (concat (mux (sgt v_17190 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17190 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17190 16 32))) (concat (mux (sgt v_17200 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17200 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17200 16 32))) (concat (mux (sgt v_17211 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17211 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17211 16 32))) (concat (mux (sgt v_17221 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17221 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17221 16 32))) (concat (mux (sgt v_17231 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17231 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17231 16 32))) (mux (sgt v_17241 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17241 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17241 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3268 : Mem) (v_3269 : reg (bv 256)) (v_3270 : reg (bv 256)) => do
      v_17255 <- evaluateAddress v_3268;
      v_17256 <- load v_17255 32;
      v_17261 <- eval (add (sext (extract v_17256 0 16) 32) (sext (extract v_17256 16 32) 32));
      v_17271 <- eval (add (sext (extract v_17256 32 48) 32) (sext (extract v_17256 48 64) 32));
      v_17281 <- eval (add (sext (extract v_17256 64 80) 32) (sext (extract v_17256 80 96) 32));
      v_17291 <- eval (add (sext (extract v_17256 96 112) 32) (sext (extract v_17256 112 128) 32));
      v_17297 <- getRegister v_3269;
      v_17302 <- eval (add (sext (extract v_17297 0 16) 32) (sext (extract v_17297 16 32) 32));
      v_17312 <- eval (add (sext (extract v_17297 32 48) 32) (sext (extract v_17297 48 64) 32));
      v_17322 <- eval (add (sext (extract v_17297 64 80) 32) (sext (extract v_17297 80 96) 32));
      v_17332 <- eval (add (sext (extract v_17297 96 112) 32) (sext (extract v_17297 112 128) 32));
      v_17342 <- eval (add (sext (extract v_17256 128 144) 32) (sext (extract v_17256 144 160) 32));
      v_17352 <- eval (add (sext (extract v_17256 160 176) 32) (sext (extract v_17256 176 192) 32));
      v_17362 <- eval (add (sext (extract v_17256 192 208) 32) (sext (extract v_17256 208 224) 32));
      v_17372 <- eval (add (sext (extract v_17256 224 240) 32) (sext (extract v_17256 240 256) 32));
      v_17382 <- eval (add (sext (extract v_17297 128 144) 32) (sext (extract v_17297 144 160) 32));
      v_17392 <- eval (add (sext (extract v_17297 160 176) 32) (sext (extract v_17297 176 192) 32));
      v_17402 <- eval (add (sext (extract v_17297 192 208) 32) (sext (extract v_17297 208 224) 32));
      v_17412 <- eval (add (sext (extract v_17297 240 256) 32) (sext (extract v_17297 224 240) 32));
      setRegister (lhs.of_reg v_3270) (concat (mux (sgt v_17261 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17261 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17261 16 32))) (concat (mux (sgt v_17271 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17271 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17271 16 32))) (concat (mux (sgt v_17281 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17281 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17281 16 32))) (concat (mux (sgt v_17291 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17291 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17291 16 32))) (concat (mux (sgt v_17302 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17302 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17302 16 32))) (concat (mux (sgt v_17312 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17312 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17312 16 32))) (concat (mux (sgt v_17322 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17322 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17322 16 32))) (concat (mux (sgt v_17332 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17332 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17332 16 32))) (concat (mux (sgt v_17342 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17342 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17342 16 32))) (concat (mux (sgt v_17352 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17352 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17352 16 32))) (concat (mux (sgt v_17362 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17362 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17362 16 32))) (concat (mux (sgt v_17372 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17372 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17372 16 32))) (concat (mux (sgt v_17382 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17382 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17382 16 32))) (concat (mux (sgt v_17392 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17392 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17392 16 32))) (concat (mux (sgt v_17402 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17402 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17402 16 32))) (mux (sgt v_17412 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17412 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17412 16 32))))))))))))))))));
      pure ()
    pat_end
