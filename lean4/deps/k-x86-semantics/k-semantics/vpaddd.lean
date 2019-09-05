def vpaddd1 : instruction :=
  definst "vpaddd" $ do
    pattern fun (v_3407 : reg (bv 128)) (v_3408 : reg (bv 128)) (v_3409 : reg (bv 128)) => do
      v_7180 <- getRegister v_3408;
      v_7182 <- getRegister v_3407;
      setRegister (lhs.of_reg v_3409) (concat (add (extract v_7180 0 32) (extract v_7182 0 32)) (concat (add (extract v_7180 32 64) (extract v_7182 32 64)) (concat (add (extract v_7180 64 96) (extract v_7182 64 96)) (add (extract v_7180 96 128) (extract v_7182 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3419 : reg (bv 256)) (v_3420 : reg (bv 256)) (v_3421 : reg (bv 256)) => do
      v_7203 <- getRegister v_3420;
      v_7205 <- getRegister v_3419;
      setRegister (lhs.of_reg v_3421) (concat (add (extract v_7203 0 32) (extract v_7205 0 32)) (concat (add (extract v_7203 32 64) (extract v_7205 32 64)) (concat (add (extract v_7203 64 96) (extract v_7205 64 96)) (concat (add (extract v_7203 96 128) (extract v_7205 96 128)) (concat (add (extract v_7203 128 160) (extract v_7205 128 160)) (concat (add (extract v_7203 160 192) (extract v_7205 160 192)) (concat (add (extract v_7203 192 224) (extract v_7205 192 224)) (add (extract v_7203 224 256) (extract v_7205 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3402 : Mem) (v_3403 : reg (bv 128)) (v_3404 : reg (bv 128)) => do
      v_12212 <- getRegister v_3403;
      v_12214 <- evaluateAddress v_3402;
      v_12215 <- load v_12214 16;
      setRegister (lhs.of_reg v_3404) (concat (add (extract v_12212 0 32) (extract v_12215 0 32)) (concat (add (extract v_12212 32 64) (extract v_12215 32 64)) (concat (add (extract v_12212 64 96) (extract v_12215 64 96)) (add (extract v_12212 96 128) (extract v_12215 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3413 : Mem) (v_3414 : reg (bv 256)) (v_3415 : reg (bv 256)) => do
      v_12231 <- getRegister v_3414;
      v_12233 <- evaluateAddress v_3413;
      v_12234 <- load v_12233 32;
      setRegister (lhs.of_reg v_3415) (concat (add (extract v_12231 0 32) (extract v_12234 0 32)) (concat (add (extract v_12231 32 64) (extract v_12234 32 64)) (concat (add (extract v_12231 64 96) (extract v_12234 64 96)) (concat (add (extract v_12231 96 128) (extract v_12234 96 128)) (concat (add (extract v_12231 128 160) (extract v_12234 128 160)) (concat (add (extract v_12231 160 192) (extract v_12234 160 192)) (concat (add (extract v_12231 192 224) (extract v_12234 192 224)) (add (extract v_12231 224 256) (extract v_12234 224 256)))))))));
      pure ()
    pat_end
