def vpackssdw1 : instruction :=
  definst "vpackssdw" $ do
    pattern fun (v_3234 : reg (bv 128)) (v_3235 : reg (bv 128)) (v_3236 : reg (bv 128)) => do
      v_6020 <- getRegister v_3234;
      v_6021 <- eval (extract v_6020 0 32);
      v_6027 <- eval (extract v_6020 32 64);
      v_6033 <- eval (extract v_6020 64 96);
      v_6039 <- eval (extract v_6020 96 128);
      v_6045 <- getRegister v_3235;
      v_6046 <- eval (extract v_6045 0 32);
      v_6052 <- eval (extract v_6045 32 64);
      v_6058 <- eval (extract v_6045 64 96);
      v_6064 <- eval (extract v_6045 96 128);
      setRegister (lhs.of_reg v_3236) (concat (mux (sgt v_6021 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6021 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6020 16 32))) (concat (mux (sgt v_6027 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6027 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6020 48 64))) (concat (mux (sgt v_6033 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6033 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6020 80 96))) (concat (mux (sgt v_6039 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6039 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6020 112 128))) (concat (mux (sgt v_6046 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6046 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6045 16 32))) (concat (mux (sgt v_6052 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6052 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6045 48 64))) (concat (mux (sgt v_6058 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6058 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6045 80 96))) (mux (sgt v_6064 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6064 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6045 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3245 : reg (bv 256)) (v_3246 : reg (bv 256)) (v_3247 : reg (bv 256)) => do
      v_6083 <- getRegister v_3245;
      v_6084 <- eval (extract v_6083 0 32);
      v_6090 <- eval (extract v_6083 32 64);
      v_6096 <- eval (extract v_6083 64 96);
      v_6102 <- eval (extract v_6083 96 128);
      v_6108 <- getRegister v_3246;
      v_6109 <- eval (extract v_6108 0 32);
      v_6115 <- eval (extract v_6108 32 64);
      v_6121 <- eval (extract v_6108 64 96);
      v_6127 <- eval (extract v_6108 96 128);
      v_6133 <- eval (extract v_6083 128 160);
      v_6139 <- eval (extract v_6083 160 192);
      v_6145 <- eval (extract v_6083 192 224);
      v_6151 <- eval (extract v_6083 224 256);
      v_6157 <- eval (extract v_6108 128 160);
      v_6163 <- eval (extract v_6108 160 192);
      v_6169 <- eval (extract v_6108 192 224);
      v_6175 <- eval (extract v_6108 224 256);
      setRegister (lhs.of_reg v_3247) (concat (mux (sgt v_6084 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6084 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 16 32))) (concat (mux (sgt v_6090 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6090 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 48 64))) (concat (mux (sgt v_6096 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6096 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 80 96))) (concat (mux (sgt v_6102 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6102 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 112 128))) (concat (mux (sgt v_6109 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6109 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 16 32))) (concat (mux (sgt v_6115 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6115 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 48 64))) (concat (mux (sgt v_6121 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6121 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 80 96))) (concat (mux (sgt v_6127 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6127 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 112 128))) (concat (mux (sgt v_6133 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6133 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 144 160))) (concat (mux (sgt v_6139 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6139 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 176 192))) (concat (mux (sgt v_6145 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6145 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 208 224))) (concat (mux (sgt v_6151 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6151 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6083 240 256))) (concat (mux (sgt v_6157 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6157 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 144 160))) (concat (mux (sgt v_6163 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6163 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 176 192))) (concat (mux (sgt v_6169 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6169 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 208 224))) (mux (sgt v_6175 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6175 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6108 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3228 : Mem) (v_3229 : reg (bv 128)) (v_3230 : reg (bv 128)) => do
      v_11284 <- evaluateAddress v_3228;
      v_11285 <- load v_11284 16;
      v_11286 <- eval (extract v_11285 0 32);
      v_11292 <- eval (extract v_11285 32 64);
      v_11298 <- eval (extract v_11285 64 96);
      v_11304 <- eval (extract v_11285 96 128);
      v_11310 <- getRegister v_3229;
      v_11311 <- eval (extract v_11310 0 32);
      v_11317 <- eval (extract v_11310 32 64);
      v_11323 <- eval (extract v_11310 64 96);
      v_11329 <- eval (extract v_11310 96 128);
      setRegister (lhs.of_reg v_3230) (concat (mux (sgt v_11286 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11286 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11285 16 32))) (concat (mux (sgt v_11292 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11292 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11285 48 64))) (concat (mux (sgt v_11298 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11298 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11285 80 96))) (concat (mux (sgt v_11304 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11304 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11285 112 128))) (concat (mux (sgt v_11311 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11311 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11310 16 32))) (concat (mux (sgt v_11317 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11317 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11310 48 64))) (concat (mux (sgt v_11323 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11323 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11310 80 96))) (mux (sgt v_11329 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11329 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11310 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3240 : reg (bv 256)) (v_3241 : reg (bv 256)) => do
      v_11343 <- evaluateAddress v_3239;
      v_11344 <- load v_11343 32;
      v_11345 <- eval (extract v_11344 0 32);
      v_11351 <- eval (extract v_11344 32 64);
      v_11357 <- eval (extract v_11344 64 96);
      v_11363 <- eval (extract v_11344 96 128);
      v_11369 <- getRegister v_3240;
      v_11370 <- eval (extract v_11369 0 32);
      v_11376 <- eval (extract v_11369 32 64);
      v_11382 <- eval (extract v_11369 64 96);
      v_11388 <- eval (extract v_11369 96 128);
      v_11394 <- eval (extract v_11344 128 160);
      v_11400 <- eval (extract v_11344 160 192);
      v_11406 <- eval (extract v_11344 192 224);
      v_11412 <- eval (extract v_11344 224 256);
      v_11418 <- eval (extract v_11369 128 160);
      v_11424 <- eval (extract v_11369 160 192);
      v_11430 <- eval (extract v_11369 192 224);
      v_11436 <- eval (extract v_11369 224 256);
      setRegister (lhs.of_reg v_3241) (concat (mux (sgt v_11345 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11345 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 16 32))) (concat (mux (sgt v_11351 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11351 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 48 64))) (concat (mux (sgt v_11357 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11357 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 80 96))) (concat (mux (sgt v_11363 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11363 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 112 128))) (concat (mux (sgt v_11370 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11370 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 16 32))) (concat (mux (sgt v_11376 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11376 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 48 64))) (concat (mux (sgt v_11382 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11382 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 80 96))) (concat (mux (sgt v_11388 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11388 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 112 128))) (concat (mux (sgt v_11394 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11394 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 144 160))) (concat (mux (sgt v_11400 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11400 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 176 192))) (concat (mux (sgt v_11406 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11406 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 208 224))) (concat (mux (sgt v_11412 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11412 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11344 240 256))) (concat (mux (sgt v_11418 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11418 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 144 160))) (concat (mux (sgt v_11424 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11424 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 176 192))) (concat (mux (sgt v_11430 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11430 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 208 224))) (mux (sgt v_11436 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11436 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11369 240 256))))))))))))))))));
      pure ()
    pat_end
