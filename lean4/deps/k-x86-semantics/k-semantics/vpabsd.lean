def vpabsd1 : instruction :=
  definst "vpabsd" $ do
    pattern fun (v_3209 : reg (bv 128)) (v_3210 : reg (bv 128)) => do
      v_6228 <- getRegister v_3209;
      v_6229 <- eval (extract v_6228 0 32);
      v_6234 <- eval (extract v_6228 32 64);
      v_6239 <- eval (extract v_6228 64 96);
      v_6244 <- eval (extract v_6228 96 128);
      setRegister (lhs.of_reg v_3210) (concat (mux (ugt v_6229 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6229 (expression.bv_nat 32 4294967295))) v_6229) (concat (mux (ugt v_6234 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6234 (expression.bv_nat 32 4294967295))) v_6234) (concat (mux (ugt v_6239 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6239 (expression.bv_nat 32 4294967295))) v_6239) (mux (ugt v_6244 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6244 (expression.bv_nat 32 4294967295))) v_6244))));
      pure ()
    pat_end;
    pattern fun (v_3218 : reg (bv 256)) (v_3219 : reg (bv 256)) => do
      v_6257 <- getRegister v_3218;
      v_6258 <- eval (extract v_6257 0 32);
      v_6263 <- eval (extract v_6257 32 64);
      v_6268 <- eval (extract v_6257 64 96);
      v_6273 <- eval (extract v_6257 96 128);
      v_6278 <- eval (extract v_6257 128 160);
      v_6283 <- eval (extract v_6257 160 192);
      v_6288 <- eval (extract v_6257 192 224);
      v_6293 <- eval (extract v_6257 224 256);
      setRegister (lhs.of_reg v_3219) (concat (mux (ugt v_6258 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6258 (expression.bv_nat 32 4294967295))) v_6258) (concat (mux (ugt v_6263 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6263 (expression.bv_nat 32 4294967295))) v_6263) (concat (mux (ugt v_6268 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6268 (expression.bv_nat 32 4294967295))) v_6268) (concat (mux (ugt v_6273 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6273 (expression.bv_nat 32 4294967295))) v_6273) (concat (mux (ugt v_6278 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6278 (expression.bv_nat 32 4294967295))) v_6278) (concat (mux (ugt v_6283 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6283 (expression.bv_nat 32 4294967295))) v_6283) (concat (mux (ugt v_6288 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6288 (expression.bv_nat 32 4294967295))) v_6288) (mux (ugt v_6293 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6293 (expression.bv_nat 32 4294967295))) v_6293))))))));
      pure ()
    pat_end;
    pattern fun (v_3205 : Mem) (v_3206 : reg (bv 128)) => do
      v_11937 <- evaluateAddress v_3205;
      v_11938 <- load v_11937 16;
      v_11939 <- eval (extract v_11938 0 32);
      v_11944 <- eval (extract v_11938 32 64);
      v_11949 <- eval (extract v_11938 64 96);
      v_11954 <- eval (extract v_11938 96 128);
      setRegister (lhs.of_reg v_3206) (concat (mux (ugt v_11939 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11939 (expression.bv_nat 32 4294967295))) v_11939) (concat (mux (ugt v_11944 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11944 (expression.bv_nat 32 4294967295))) v_11944) (concat (mux (ugt v_11949 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11949 (expression.bv_nat 32 4294967295))) v_11949) (mux (ugt v_11954 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11954 (expression.bv_nat 32 4294967295))) v_11954))));
      pure ()
    pat_end;
    pattern fun (v_3214 : Mem) (v_3215 : reg (bv 256)) => do
      v_11963 <- evaluateAddress v_3214;
      v_11964 <- load v_11963 32;
      v_11965 <- eval (extract v_11964 0 32);
      v_11970 <- eval (extract v_11964 32 64);
      v_11975 <- eval (extract v_11964 64 96);
      v_11980 <- eval (extract v_11964 96 128);
      v_11985 <- eval (extract v_11964 128 160);
      v_11990 <- eval (extract v_11964 160 192);
      v_11995 <- eval (extract v_11964 192 224);
      v_12000 <- eval (extract v_11964 224 256);
      setRegister (lhs.of_reg v_3215) (concat (mux (ugt v_11965 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11965 (expression.bv_nat 32 4294967295))) v_11965) (concat (mux (ugt v_11970 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11970 (expression.bv_nat 32 4294967295))) v_11970) (concat (mux (ugt v_11975 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11975 (expression.bv_nat 32 4294967295))) v_11975) (concat (mux (ugt v_11980 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11980 (expression.bv_nat 32 4294967295))) v_11980) (concat (mux (ugt v_11985 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11985 (expression.bv_nat 32 4294967295))) v_11985) (concat (mux (ugt v_11990 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11990 (expression.bv_nat 32 4294967295))) v_11990) (concat (mux (ugt v_11995 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11995 (expression.bv_nat 32 4294967295))) v_11995) (mux (ugt v_12000 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_12000 (expression.bv_nat 32 4294967295))) v_12000))))))));
      pure ()
    pat_end
