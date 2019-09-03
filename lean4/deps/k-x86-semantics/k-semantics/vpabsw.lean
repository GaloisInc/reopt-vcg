def vpabsw1 : instruction :=
  definst "vpabsw" $ do
    pattern fun (v_3227 : reg (bv 128)) (v_3228 : reg (bv 128)) => do
      v_6310 <- getRegister v_3227;
      v_6311 <- eval (extract v_6310 0 16);
      v_6316 <- eval (extract v_6310 16 32);
      v_6321 <- eval (extract v_6310 32 48);
      v_6326 <- eval (extract v_6310 48 64);
      v_6331 <- eval (extract v_6310 64 80);
      v_6336 <- eval (extract v_6310 80 96);
      v_6341 <- eval (extract v_6310 96 112);
      v_6346 <- eval (extract v_6310 112 128);
      setRegister (lhs.of_reg v_3228) (concat (mux (ugt v_6311 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6311 (expression.bv_nat 16 65535))) v_6311) (concat (mux (ugt v_6316 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6316 (expression.bv_nat 16 65535))) v_6316) (concat (mux (ugt v_6321 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6321 (expression.bv_nat 16 65535))) v_6321) (concat (mux (ugt v_6326 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6326 (expression.bv_nat 16 65535))) v_6326) (concat (mux (ugt v_6331 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6331 (expression.bv_nat 16 65535))) v_6331) (concat (mux (ugt v_6336 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6336 (expression.bv_nat 16 65535))) v_6336) (concat (mux (ugt v_6341 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6341 (expression.bv_nat 16 65535))) v_6341) (mux (ugt v_6346 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6346 (expression.bv_nat 16 65535))) v_6346))))))));
      pure ()
    pat_end;
    pattern fun (v_3236 : reg (bv 256)) (v_3237 : reg (bv 256)) => do
      v_6363 <- getRegister v_3236;
      v_6364 <- eval (extract v_6363 0 16);
      v_6369 <- eval (extract v_6363 16 32);
      v_6374 <- eval (extract v_6363 32 48);
      v_6379 <- eval (extract v_6363 48 64);
      v_6384 <- eval (extract v_6363 64 80);
      v_6389 <- eval (extract v_6363 80 96);
      v_6394 <- eval (extract v_6363 96 112);
      v_6399 <- eval (extract v_6363 112 128);
      v_6404 <- eval (extract v_6363 128 144);
      v_6409 <- eval (extract v_6363 144 160);
      v_6414 <- eval (extract v_6363 160 176);
      v_6419 <- eval (extract v_6363 176 192);
      v_6424 <- eval (extract v_6363 192 208);
      v_6429 <- eval (extract v_6363 208 224);
      v_6434 <- eval (extract v_6363 224 240);
      v_6439 <- eval (extract v_6363 240 256);
      setRegister (lhs.of_reg v_3237) (concat (mux (ugt v_6364 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6364 (expression.bv_nat 16 65535))) v_6364) (concat (mux (ugt v_6369 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6369 (expression.bv_nat 16 65535))) v_6369) (concat (mux (ugt v_6374 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6374 (expression.bv_nat 16 65535))) v_6374) (concat (mux (ugt v_6379 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6379 (expression.bv_nat 16 65535))) v_6379) (concat (mux (ugt v_6384 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6384 (expression.bv_nat 16 65535))) v_6384) (concat (mux (ugt v_6389 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6389 (expression.bv_nat 16 65535))) v_6389) (concat (mux (ugt v_6394 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6394 (expression.bv_nat 16 65535))) v_6394) (concat (mux (ugt v_6399 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6399 (expression.bv_nat 16 65535))) v_6399) (concat (mux (ugt v_6404 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6404 (expression.bv_nat 16 65535))) v_6404) (concat (mux (ugt v_6409 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6409 (expression.bv_nat 16 65535))) v_6409) (concat (mux (ugt v_6414 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6414 (expression.bv_nat 16 65535))) v_6414) (concat (mux (ugt v_6419 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6419 (expression.bv_nat 16 65535))) v_6419) (concat (mux (ugt v_6424 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6424 (expression.bv_nat 16 65535))) v_6424) (concat (mux (ugt v_6429 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6429 (expression.bv_nat 16 65535))) v_6429) (concat (mux (ugt v_6434 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6434 (expression.bv_nat 16 65535))) v_6434) (mux (ugt v_6439 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6439 (expression.bv_nat 16 65535))) v_6439))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3223 : Mem) (v_3224 : reg (bv 128)) => do
      v_12013 <- evaluateAddress v_3223;
      v_12014 <- load v_12013 16;
      v_12015 <- eval (extract v_12014 0 16);
      v_12020 <- eval (extract v_12014 16 32);
      v_12025 <- eval (extract v_12014 32 48);
      v_12030 <- eval (extract v_12014 48 64);
      v_12035 <- eval (extract v_12014 64 80);
      v_12040 <- eval (extract v_12014 80 96);
      v_12045 <- eval (extract v_12014 96 112);
      v_12050 <- eval (extract v_12014 112 128);
      setRegister (lhs.of_reg v_3224) (concat (mux (ugt v_12015 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12015 (expression.bv_nat 16 65535))) v_12015) (concat (mux (ugt v_12020 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12020 (expression.bv_nat 16 65535))) v_12020) (concat (mux (ugt v_12025 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12025 (expression.bv_nat 16 65535))) v_12025) (concat (mux (ugt v_12030 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12030 (expression.bv_nat 16 65535))) v_12030) (concat (mux (ugt v_12035 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12035 (expression.bv_nat 16 65535))) v_12035) (concat (mux (ugt v_12040 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12040 (expression.bv_nat 16 65535))) v_12040) (concat (mux (ugt v_12045 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12045 (expression.bv_nat 16 65535))) v_12045) (mux (ugt v_12050 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12050 (expression.bv_nat 16 65535))) v_12050))))))));
      pure ()
    pat_end;
    pattern fun (v_3232 : Mem) (v_3233 : reg (bv 256)) => do
      v_12063 <- evaluateAddress v_3232;
      v_12064 <- load v_12063 32;
      v_12065 <- eval (extract v_12064 0 16);
      v_12070 <- eval (extract v_12064 16 32);
      v_12075 <- eval (extract v_12064 32 48);
      v_12080 <- eval (extract v_12064 48 64);
      v_12085 <- eval (extract v_12064 64 80);
      v_12090 <- eval (extract v_12064 80 96);
      v_12095 <- eval (extract v_12064 96 112);
      v_12100 <- eval (extract v_12064 112 128);
      v_12105 <- eval (extract v_12064 128 144);
      v_12110 <- eval (extract v_12064 144 160);
      v_12115 <- eval (extract v_12064 160 176);
      v_12120 <- eval (extract v_12064 176 192);
      v_12125 <- eval (extract v_12064 192 208);
      v_12130 <- eval (extract v_12064 208 224);
      v_12135 <- eval (extract v_12064 224 240);
      v_12140 <- eval (extract v_12064 240 256);
      setRegister (lhs.of_reg v_3233) (concat (mux (ugt v_12065 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12065 (expression.bv_nat 16 65535))) v_12065) (concat (mux (ugt v_12070 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12070 (expression.bv_nat 16 65535))) v_12070) (concat (mux (ugt v_12075 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12075 (expression.bv_nat 16 65535))) v_12075) (concat (mux (ugt v_12080 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12080 (expression.bv_nat 16 65535))) v_12080) (concat (mux (ugt v_12085 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12085 (expression.bv_nat 16 65535))) v_12085) (concat (mux (ugt v_12090 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12090 (expression.bv_nat 16 65535))) v_12090) (concat (mux (ugt v_12095 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12095 (expression.bv_nat 16 65535))) v_12095) (concat (mux (ugt v_12100 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12100 (expression.bv_nat 16 65535))) v_12100) (concat (mux (ugt v_12105 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12105 (expression.bv_nat 16 65535))) v_12105) (concat (mux (ugt v_12110 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12110 (expression.bv_nat 16 65535))) v_12110) (concat (mux (ugt v_12115 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12115 (expression.bv_nat 16 65535))) v_12115) (concat (mux (ugt v_12120 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12120 (expression.bv_nat 16 65535))) v_12120) (concat (mux (ugt v_12125 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12125 (expression.bv_nat 16 65535))) v_12125) (concat (mux (ugt v_12130 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12130 (expression.bv_nat 16 65535))) v_12130) (concat (mux (ugt v_12135 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12135 (expression.bv_nat 16 65535))) v_12135) (mux (ugt v_12140 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12140 (expression.bv_nat 16 65535))) v_12140))))))))))))))));
      pure ()
    pat_end
