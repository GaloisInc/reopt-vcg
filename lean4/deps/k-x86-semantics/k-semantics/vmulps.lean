def vmulps1 : instruction :=
  definst "vmulps" $ do
    pattern fun (v_3104 : reg (bv 128)) (v_3105 : reg (bv 128)) (v_3106 : reg (bv 128)) => do
      v_5597 <- getRegister v_3105;
      v_5598 <- eval (extract v_5597 0 32);
      v_5606 <- getRegister v_3104;
      v_5607 <- eval (extract v_5606 0 32);
      v_5617 <- eval (extract v_5597 32 64);
      v_5625 <- eval (extract v_5606 32 64);
      v_5635 <- eval (extract v_5597 64 96);
      v_5643 <- eval (extract v_5606 64 96);
      v_5653 <- eval (extract v_5597 96 128);
      v_5661 <- eval (extract v_5606 96 128);
      setRegister (lhs.of_reg v_3106) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5598 0 1)) (uvalueMInt (extract v_5598 1 9)) (uvalueMInt (extract v_5598 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5607 0 1)) (uvalueMInt (extract v_5607 1 9)) (uvalueMInt (extract v_5607 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5617 0 1)) (uvalueMInt (extract v_5617 1 9)) (uvalueMInt (extract v_5617 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5625 0 1)) (uvalueMInt (extract v_5625 1 9)) (uvalueMInt (extract v_5625 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5635 0 1)) (uvalueMInt (extract v_5635 1 9)) (uvalueMInt (extract v_5635 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5643 0 1)) (uvalueMInt (extract v_5643 1 9)) (uvalueMInt (extract v_5643 9 32)))) 32) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5653 0 1)) (uvalueMInt (extract v_5653 1 9)) (uvalueMInt (extract v_5653 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5661 0 1)) (uvalueMInt (extract v_5661 1 9)) (uvalueMInt (extract v_5661 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3115 : reg (bv 256)) (v_3116 : reg (bv 256)) (v_3117 : reg (bv 256)) => do
      v_5680 <- getRegister v_3116;
      v_5681 <- eval (extract v_5680 0 32);
      v_5689 <- getRegister v_3115;
      v_5690 <- eval (extract v_5689 0 32);
      v_5700 <- eval (extract v_5680 32 64);
      v_5708 <- eval (extract v_5689 32 64);
      v_5718 <- eval (extract v_5680 64 96);
      v_5726 <- eval (extract v_5689 64 96);
      v_5736 <- eval (extract v_5680 96 128);
      v_5744 <- eval (extract v_5689 96 128);
      v_5754 <- eval (extract v_5680 128 160);
      v_5762 <- eval (extract v_5689 128 160);
      v_5772 <- eval (extract v_5680 160 192);
      v_5780 <- eval (extract v_5689 160 192);
      v_5790 <- eval (extract v_5680 192 224);
      v_5798 <- eval (extract v_5689 192 224);
      v_5808 <- eval (extract v_5680 224 256);
      v_5816 <- eval (extract v_5689 224 256);
      setRegister (lhs.of_reg v_3117) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5681 0 1)) (uvalueMInt (extract v_5681 1 9)) (uvalueMInt (extract v_5681 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5690 0 1)) (uvalueMInt (extract v_5690 1 9)) (uvalueMInt (extract v_5690 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5700 0 1)) (uvalueMInt (extract v_5700 1 9)) (uvalueMInt (extract v_5700 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5708 0 1)) (uvalueMInt (extract v_5708 1 9)) (uvalueMInt (extract v_5708 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5718 0 1)) (uvalueMInt (extract v_5718 1 9)) (uvalueMInt (extract v_5718 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5726 0 1)) (uvalueMInt (extract v_5726 1 9)) (uvalueMInt (extract v_5726 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5736 0 1)) (uvalueMInt (extract v_5736 1 9)) (uvalueMInt (extract v_5736 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5744 0 1)) (uvalueMInt (extract v_5744 1 9)) (uvalueMInt (extract v_5744 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5754 0 1)) (uvalueMInt (extract v_5754 1 9)) (uvalueMInt (extract v_5754 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5762 0 1)) (uvalueMInt (extract v_5762 1 9)) (uvalueMInt (extract v_5762 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5772 0 1)) (uvalueMInt (extract v_5772 1 9)) (uvalueMInt (extract v_5772 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5780 0 1)) (uvalueMInt (extract v_5780 1 9)) (uvalueMInt (extract v_5780 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5790 0 1)) (uvalueMInt (extract v_5790 1 9)) (uvalueMInt (extract v_5790 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5798 0 1)) (uvalueMInt (extract v_5798 1 9)) (uvalueMInt (extract v_5798 9 32)))) 32) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5808 0 1)) (uvalueMInt (extract v_5808 1 9)) (uvalueMInt (extract v_5808 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5816 0 1)) (uvalueMInt (extract v_5816 1 9)) (uvalueMInt (extract v_5816 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3099 : Mem) (v_3100 : reg (bv 128)) (v_3101 : reg (bv 128)) => do
      v_11345 <- getRegister v_3100;
      v_11346 <- eval (extract v_11345 0 32);
      v_11354 <- evaluateAddress v_3099;
      v_11355 <- load v_11354 16;
      v_11356 <- eval (extract v_11355 0 32);
      v_11366 <- eval (extract v_11345 32 64);
      v_11374 <- eval (extract v_11355 32 64);
      v_11384 <- eval (extract v_11345 64 96);
      v_11392 <- eval (extract v_11355 64 96);
      v_11402 <- eval (extract v_11345 96 128);
      v_11410 <- eval (extract v_11355 96 128);
      setRegister (lhs.of_reg v_3101) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11346 0 1)) (uvalueMInt (extract v_11346 1 9)) (uvalueMInt (extract v_11346 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11356 0 1)) (uvalueMInt (extract v_11356 1 9)) (uvalueMInt (extract v_11356 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11366 0 1)) (uvalueMInt (extract v_11366 1 9)) (uvalueMInt (extract v_11366 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11374 0 1)) (uvalueMInt (extract v_11374 1 9)) (uvalueMInt (extract v_11374 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11384 0 1)) (uvalueMInt (extract v_11384 1 9)) (uvalueMInt (extract v_11384 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11392 0 1)) (uvalueMInt (extract v_11392 1 9)) (uvalueMInt (extract v_11392 9 32)))) 32) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11402 0 1)) (uvalueMInt (extract v_11402 1 9)) (uvalueMInt (extract v_11402 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11410 0 1)) (uvalueMInt (extract v_11410 1 9)) (uvalueMInt (extract v_11410 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3110 : Mem) (v_3111 : reg (bv 256)) (v_3112 : reg (bv 256)) => do
      v_11424 <- getRegister v_3111;
      v_11425 <- eval (extract v_11424 0 32);
      v_11433 <- evaluateAddress v_3110;
      v_11434 <- load v_11433 32;
      v_11435 <- eval (extract v_11434 0 32);
      v_11445 <- eval (extract v_11424 32 64);
      v_11453 <- eval (extract v_11434 32 64);
      v_11463 <- eval (extract v_11424 64 96);
      v_11471 <- eval (extract v_11434 64 96);
      v_11481 <- eval (extract v_11424 96 128);
      v_11489 <- eval (extract v_11434 96 128);
      v_11499 <- eval (extract v_11424 128 160);
      v_11507 <- eval (extract v_11434 128 160);
      v_11517 <- eval (extract v_11424 160 192);
      v_11525 <- eval (extract v_11434 160 192);
      v_11535 <- eval (extract v_11424 192 224);
      v_11543 <- eval (extract v_11434 192 224);
      v_11553 <- eval (extract v_11424 224 256);
      v_11561 <- eval (extract v_11434 224 256);
      setRegister (lhs.of_reg v_3112) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11425 0 1)) (uvalueMInt (extract v_11425 1 9)) (uvalueMInt (extract v_11425 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11435 0 1)) (uvalueMInt (extract v_11435 1 9)) (uvalueMInt (extract v_11435 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11445 0 1)) (uvalueMInt (extract v_11445 1 9)) (uvalueMInt (extract v_11445 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11453 0 1)) (uvalueMInt (extract v_11453 1 9)) (uvalueMInt (extract v_11453 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11463 0 1)) (uvalueMInt (extract v_11463 1 9)) (uvalueMInt (extract v_11463 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11471 0 1)) (uvalueMInt (extract v_11471 1 9)) (uvalueMInt (extract v_11471 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11481 0 1)) (uvalueMInt (extract v_11481 1 9)) (uvalueMInt (extract v_11481 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11489 0 1)) (uvalueMInt (extract v_11489 1 9)) (uvalueMInt (extract v_11489 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11499 0 1)) (uvalueMInt (extract v_11499 1 9)) (uvalueMInt (extract v_11499 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11507 0 1)) (uvalueMInt (extract v_11507 1 9)) (uvalueMInt (extract v_11507 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11517 0 1)) (uvalueMInt (extract v_11517 1 9)) (uvalueMInt (extract v_11517 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11525 0 1)) (uvalueMInt (extract v_11525 1 9)) (uvalueMInt (extract v_11525 9 32)))) 32) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11535 0 1)) (uvalueMInt (extract v_11535 1 9)) (uvalueMInt (extract v_11535 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11543 0 1)) (uvalueMInt (extract v_11543 1 9)) (uvalueMInt (extract v_11543 9 32)))) 32) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11553 0 1)) (uvalueMInt (extract v_11553 1 9)) (uvalueMInt (extract v_11553 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11561 0 1)) (uvalueMInt (extract v_11561 1 9)) (uvalueMInt (extract v_11561 9 32)))) 32))))))));
      pure ()
    pat_end
