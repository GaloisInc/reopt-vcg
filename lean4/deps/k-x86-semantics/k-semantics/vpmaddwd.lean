def vpmaddwd1 : instruction :=
  definst "vpmaddwd" $ do
    pattern fun (v_3455 : reg (bv 128)) (v_3456 : reg (bv 128)) (v_3457 : reg (bv 128)) => do
      v_10188 <- getRegister v_3455;
      v_10191 <- getRegister v_3456;
      setRegister (lhs.of_reg v_3457) (concat (add (mul (sext (extract v_10188 16 32) 32) (sext (extract v_10191 16 32) 32)) (mul (sext (extract v_10188 0 16) 32) (sext (extract v_10191 0 16) 32))) (concat (add (mul (sext (extract v_10188 48 64) 32) (sext (extract v_10191 48 64) 32)) (mul (sext (extract v_10188 32 48) 32) (sext (extract v_10191 32 48) 32))) (concat (add (mul (sext (extract v_10188 80 96) 32) (sext (extract v_10191 80 96) 32)) (mul (sext (extract v_10188 64 80) 32) (sext (extract v_10191 64 80) 32))) (add (mul (sext (extract v_10188 112 128) 32) (sext (extract v_10191 112 128) 32)) (mul (sext (extract v_10188 96 112) 32) (sext (extract v_10191 96 112) 32))))));
      pure ()
    pat_end;
    pattern fun (v_3466 : reg (bv 256)) (v_3467 : reg (bv 256)) (v_3468 : reg (bv 256)) => do
      v_10243 <- getRegister v_3466;
      v_10246 <- getRegister v_3467;
      setRegister (lhs.of_reg v_3468) (concat (add (mul (sext (extract v_10243 16 32) 32) (sext (extract v_10246 16 32) 32)) (mul (sext (extract v_10243 0 16) 32) (sext (extract v_10246 0 16) 32))) (concat (add (mul (sext (extract v_10243 48 64) 32) (sext (extract v_10246 48 64) 32)) (mul (sext (extract v_10243 32 48) 32) (sext (extract v_10246 32 48) 32))) (concat (add (mul (sext (extract v_10243 80 96) 32) (sext (extract v_10246 80 96) 32)) (mul (sext (extract v_10243 64 80) 32) (sext (extract v_10246 64 80) 32))) (concat (add (mul (sext (extract v_10243 112 128) 32) (sext (extract v_10246 112 128) 32)) (mul (sext (extract v_10243 96 112) 32) (sext (extract v_10246 96 112) 32))) (concat (add (mul (sext (extract v_10243 144 160) 32) (sext (extract v_10246 144 160) 32)) (mul (sext (extract v_10243 128 144) 32) (sext (extract v_10246 128 144) 32))) (concat (add (mul (sext (extract v_10243 176 192) 32) (sext (extract v_10246 176 192) 32)) (mul (sext (extract v_10243 160 176) 32) (sext (extract v_10246 160 176) 32))) (concat (add (mul (sext (extract v_10243 208 224) 32) (sext (extract v_10246 208 224) 32)) (mul (sext (extract v_10243 192 208) 32) (sext (extract v_10246 192 208) 32))) (add (mul (sext (extract v_10243 240 256) 32) (sext (extract v_10246 240 256) 32)) (mul (sext (extract v_10243 224 240) 32) (sext (extract v_10246 224 240) 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3450 : Mem) (v_3451 : reg (bv 128)) (v_3452 : reg (bv 128)) => do
      v_18529 <- evaluateAddress v_3450;
      v_18530 <- load v_18529 16;
      v_18533 <- getRegister v_3451;
      setRegister (lhs.of_reg v_3452) (concat (add (mul (sext (extract v_18530 16 32) 32) (sext (extract v_18533 16 32) 32)) (mul (sext (extract v_18530 0 16) 32) (sext (extract v_18533 0 16) 32))) (concat (add (mul (sext (extract v_18530 48 64) 32) (sext (extract v_18533 48 64) 32)) (mul (sext (extract v_18530 32 48) 32) (sext (extract v_18533 32 48) 32))) (concat (add (mul (sext (extract v_18530 80 96) 32) (sext (extract v_18533 80 96) 32)) (mul (sext (extract v_18530 64 80) 32) (sext (extract v_18533 64 80) 32))) (add (mul (sext (extract v_18530 112 128) 32) (sext (extract v_18533 112 128) 32)) (mul (sext (extract v_18530 96 112) 32) (sext (extract v_18533 96 112) 32))))));
      pure ()
    pat_end;
    pattern fun (v_3461 : Mem) (v_3462 : reg (bv 256)) (v_3463 : reg (bv 256)) => do
      v_18580 <- evaluateAddress v_3461;
      v_18581 <- load v_18580 32;
      v_18584 <- getRegister v_3462;
      setRegister (lhs.of_reg v_3463) (concat (add (mul (sext (extract v_18581 16 32) 32) (sext (extract v_18584 16 32) 32)) (mul (sext (extract v_18581 0 16) 32) (sext (extract v_18584 0 16) 32))) (concat (add (mul (sext (extract v_18581 48 64) 32) (sext (extract v_18584 48 64) 32)) (mul (sext (extract v_18581 32 48) 32) (sext (extract v_18584 32 48) 32))) (concat (add (mul (sext (extract v_18581 80 96) 32) (sext (extract v_18584 80 96) 32)) (mul (sext (extract v_18581 64 80) 32) (sext (extract v_18584 64 80) 32))) (concat (add (mul (sext (extract v_18581 112 128) 32) (sext (extract v_18584 112 128) 32)) (mul (sext (extract v_18581 96 112) 32) (sext (extract v_18584 96 112) 32))) (concat (add (mul (sext (extract v_18581 144 160) 32) (sext (extract v_18584 144 160) 32)) (mul (sext (extract v_18581 128 144) 32) (sext (extract v_18584 128 144) 32))) (concat (add (mul (sext (extract v_18581 176 192) 32) (sext (extract v_18584 176 192) 32)) (mul (sext (extract v_18581 160 176) 32) (sext (extract v_18584 160 176) 32))) (concat (add (mul (sext (extract v_18581 208 224) 32) (sext (extract v_18584 208 224) 32)) (mul (sext (extract v_18581 192 208) 32) (sext (extract v_18584 192 208) 32))) (add (mul (sext (extract v_18581 240 256) 32) (sext (extract v_18584 240 256) 32)) (mul (sext (extract v_18581 224 240) 32) (sext (extract v_18584 224 240) 32))))))))));
      pure ()
    pat_end
