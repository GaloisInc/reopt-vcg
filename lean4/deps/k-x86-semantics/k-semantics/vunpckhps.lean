def vunpckhps1 : instruction :=
  definst "vunpckhps" $ do
    pattern fun (v_3222 : reg (bv 128)) (v_3223 : reg (bv 128)) (v_3224 : reg (bv 128)) => do
      v_7542 <- getRegister v_3222;
      v_7544 <- getRegister v_3223;
      setRegister (lhs.of_reg v_3224) (concat (concat (concat (extract v_7542 0 32) (extract v_7544 0 32)) (extract v_7542 32 64)) (extract v_7544 32 64));
      pure ()
    pat_end;
    pattern fun (v_3233 : reg (bv 256)) (v_3234 : reg (bv 256)) (v_3235 : reg (bv 256)) => do
      v_7557 <- getRegister v_3233;
      v_7559 <- getRegister v_3234;
      setRegister (lhs.of_reg v_3235) (concat (concat (concat (concat (extract v_7557 0 32) (extract v_7559 0 32)) (extract v_7557 32 64)) (extract v_7559 32 64)) (concat (concat (concat (extract v_7557 128 160) (extract v_7559 128 160)) (extract v_7557 160 192)) (extract v_7559 160 192)));
      pure ()
    pat_end;
    pattern fun (v_3216 : Mem) (v_3217 : reg (bv 128)) (v_3218 : reg (bv 128)) => do
      v_13414 <- evaluateAddress v_3216;
      v_13415 <- load v_13414 16;
      v_13417 <- getRegister v_3217;
      setRegister (lhs.of_reg v_3218) (concat (concat (concat (extract v_13415 0 32) (extract v_13417 0 32)) (extract v_13415 32 64)) (extract v_13417 32 64));
      pure ()
    pat_end;
    pattern fun (v_3227 : Mem) (v_3228 : reg (bv 256)) (v_3229 : reg (bv 256)) => do
      v_13425 <- evaluateAddress v_3227;
      v_13426 <- load v_13425 32;
      v_13428 <- getRegister v_3228;
      setRegister (lhs.of_reg v_3229) (concat (concat (concat (concat (extract v_13426 0 32) (extract v_13428 0 32)) (extract v_13426 32 64)) (extract v_13428 32 64)) (concat (concat (concat (extract v_13426 128 160) (extract v_13428 128 160)) (extract v_13426 160 192)) (extract v_13428 160 192)));
      pure ()
    pat_end
