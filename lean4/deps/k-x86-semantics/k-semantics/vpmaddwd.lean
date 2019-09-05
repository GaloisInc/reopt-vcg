def vpmaddwd1 : instruction :=
  definst "vpmaddwd" $ do
    pattern fun (v_3429 : reg (bv 128)) (v_3430 : reg (bv 128)) (v_3431 : reg (bv 128)) => do
      v_10161 <- getRegister v_3429;
      v_10164 <- getRegister v_3430;
      setRegister (lhs.of_reg v_3431) (concat (add (mul (sext (extract v_10161 16 32) 32) (sext (extract v_10164 16 32) 32)) (mul (sext (extract v_10161 0 16) 32) (sext (extract v_10164 0 16) 32))) (concat (add (mul (sext (extract v_10161 48 64) 32) (sext (extract v_10164 48 64) 32)) (mul (sext (extract v_10161 32 48) 32) (sext (extract v_10164 32 48) 32))) (concat (add (mul (sext (extract v_10161 80 96) 32) (sext (extract v_10164 80 96) 32)) (mul (sext (extract v_10161 64 80) 32) (sext (extract v_10164 64 80) 32))) (add (mul (sext (extract v_10161 112 128) 32) (sext (extract v_10164 112 128) 32)) (mul (sext (extract v_10161 96 112) 32) (sext (extract v_10164 96 112) 32))))));
      pure ()
    pat_end;
    pattern fun (v_3439 : reg (bv 256)) (v_3440 : reg (bv 256)) (v_3441 : reg (bv 256)) => do
      v_10216 <- getRegister v_3439;
      v_10219 <- getRegister v_3440;
      setRegister (lhs.of_reg v_3441) (concat (add (mul (sext (extract v_10216 16 32) 32) (sext (extract v_10219 16 32) 32)) (mul (sext (extract v_10216 0 16) 32) (sext (extract v_10219 0 16) 32))) (concat (add (mul (sext (extract v_10216 48 64) 32) (sext (extract v_10219 48 64) 32)) (mul (sext (extract v_10216 32 48) 32) (sext (extract v_10219 32 48) 32))) (concat (add (mul (sext (extract v_10216 80 96) 32) (sext (extract v_10219 80 96) 32)) (mul (sext (extract v_10216 64 80) 32) (sext (extract v_10219 64 80) 32))) (concat (add (mul (sext (extract v_10216 112 128) 32) (sext (extract v_10219 112 128) 32)) (mul (sext (extract v_10216 96 112) 32) (sext (extract v_10219 96 112) 32))) (concat (add (mul (sext (extract v_10216 144 160) 32) (sext (extract v_10219 144 160) 32)) (mul (sext (extract v_10216 128 144) 32) (sext (extract v_10219 128 144) 32))) (concat (add (mul (sext (extract v_10216 176 192) 32) (sext (extract v_10219 176 192) 32)) (mul (sext (extract v_10216 160 176) 32) (sext (extract v_10219 160 176) 32))) (concat (add (mul (sext (extract v_10216 208 224) 32) (sext (extract v_10219 208 224) 32)) (mul (sext (extract v_10216 192 208) 32) (sext (extract v_10219 192 208) 32))) (add (mul (sext (extract v_10216 240 256) 32) (sext (extract v_10219 240 256) 32)) (mul (sext (extract v_10216 224 240) 32) (sext (extract v_10219 224 240) 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3423 : Mem) (v_3424 : reg (bv 128)) (v_3425 : reg (bv 128)) => do
      v_18502 <- evaluateAddress v_3423;
      v_18503 <- load v_18502 16;
      v_18506 <- getRegister v_3424;
      setRegister (lhs.of_reg v_3425) (concat (add (mul (sext (extract v_18503 16 32) 32) (sext (extract v_18506 16 32) 32)) (mul (sext (extract v_18503 0 16) 32) (sext (extract v_18506 0 16) 32))) (concat (add (mul (sext (extract v_18503 48 64) 32) (sext (extract v_18506 48 64) 32)) (mul (sext (extract v_18503 32 48) 32) (sext (extract v_18506 32 48) 32))) (concat (add (mul (sext (extract v_18503 80 96) 32) (sext (extract v_18506 80 96) 32)) (mul (sext (extract v_18503 64 80) 32) (sext (extract v_18506 64 80) 32))) (add (mul (sext (extract v_18503 112 128) 32) (sext (extract v_18506 112 128) 32)) (mul (sext (extract v_18503 96 112) 32) (sext (extract v_18506 96 112) 32))))));
      pure ()
    pat_end;
    pattern fun (v_3434 : Mem) (v_3435 : reg (bv 256)) (v_3436 : reg (bv 256)) => do
      v_18553 <- evaluateAddress v_3434;
      v_18554 <- load v_18553 32;
      v_18557 <- getRegister v_3435;
      setRegister (lhs.of_reg v_3436) (concat (add (mul (sext (extract v_18554 16 32) 32) (sext (extract v_18557 16 32) 32)) (mul (sext (extract v_18554 0 16) 32) (sext (extract v_18557 0 16) 32))) (concat (add (mul (sext (extract v_18554 48 64) 32) (sext (extract v_18557 48 64) 32)) (mul (sext (extract v_18554 32 48) 32) (sext (extract v_18557 32 48) 32))) (concat (add (mul (sext (extract v_18554 80 96) 32) (sext (extract v_18557 80 96) 32)) (mul (sext (extract v_18554 64 80) 32) (sext (extract v_18557 64 80) 32))) (concat (add (mul (sext (extract v_18554 112 128) 32) (sext (extract v_18557 112 128) 32)) (mul (sext (extract v_18554 96 112) 32) (sext (extract v_18557 96 112) 32))) (concat (add (mul (sext (extract v_18554 144 160) 32) (sext (extract v_18557 144 160) 32)) (mul (sext (extract v_18554 128 144) 32) (sext (extract v_18557 128 144) 32))) (concat (add (mul (sext (extract v_18554 176 192) 32) (sext (extract v_18557 176 192) 32)) (mul (sext (extract v_18554 160 176) 32) (sext (extract v_18557 160 176) 32))) (concat (add (mul (sext (extract v_18554 208 224) 32) (sext (extract v_18557 208 224) 32)) (mul (sext (extract v_18554 192 208) 32) (sext (extract v_18557 192 208) 32))) (add (mul (sext (extract v_18554 240 256) 32) (sext (extract v_18557 240 256) 32)) (mul (sext (extract v_18554 224 240) 32) (sext (extract v_18557 224 240) 32))))))))));
      pure ()
    pat_end
