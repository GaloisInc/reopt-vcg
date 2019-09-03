def vaddsubps1 : instruction :=
  definst "vaddsubps" $ do
    pattern fun (v_2671 : reg (bv 128)) (v_2672 : reg (bv 128)) (v_2673 : reg (bv 128)) => do
      v_5378 <- getRegister v_2672;
      v_5379 <- eval (extract v_5378 0 32);
      v_5387 <- getRegister v_2671;
      v_5388 <- eval (extract v_5387 0 32);
      v_5398 <- eval (extract v_5378 32 64);
      v_5406 <- eval (extract v_5387 32 64);
      v_5417 <- eval (extract v_5378 64 96);
      v_5425 <- eval (extract v_5387 64 96);
      v_5435 <- eval (extract v_5378 96 128);
      v_5443 <- eval (extract v_5387 96 128);
      setRegister (lhs.of_reg v_2673) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5379 0 1)) (uvalueMInt (extract v_5379 1 9)) (uvalueMInt (extract v_5379 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5388 0 1)) (uvalueMInt (extract v_5388 1 9)) (uvalueMInt (extract v_5388 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5398 0 1)) (uvalueMInt (extract v_5398 1 9)) (uvalueMInt (extract v_5398 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5406 0 1)) (uvalueMInt (extract v_5406 1 9)) (uvalueMInt (extract v_5406 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5417 0 1)) (uvalueMInt (extract v_5417 1 9)) (uvalueMInt (extract v_5417 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5425 0 1)) (uvalueMInt (extract v_5425 1 9)) (uvalueMInt (extract v_5425 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5435 0 1)) (uvalueMInt (extract v_5435 1 9)) (uvalueMInt (extract v_5435 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5443 0 1)) (uvalueMInt (extract v_5443 1 9)) (uvalueMInt (extract v_5443 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2679 : reg (bv 256)) (v_2680 : reg (bv 256)) (v_2681 : reg (bv 256)) => do
      v_5461 <- getRegister v_2680;
      v_5462 <- eval (extract v_5461 0 32);
      v_5470 <- getRegister v_2679;
      v_5471 <- eval (extract v_5470 0 32);
      v_5481 <- eval (extract v_5461 32 64);
      v_5489 <- eval (extract v_5470 32 64);
      v_5500 <- eval (extract v_5461 64 96);
      v_5508 <- eval (extract v_5470 64 96);
      v_5518 <- eval (extract v_5461 96 128);
      v_5526 <- eval (extract v_5470 96 128);
      v_5537 <- eval (extract v_5461 128 160);
      v_5545 <- eval (extract v_5470 128 160);
      v_5555 <- eval (extract v_5461 160 192);
      v_5563 <- eval (extract v_5470 160 192);
      v_5574 <- eval (extract v_5461 192 224);
      v_5582 <- eval (extract v_5470 192 224);
      v_5592 <- eval (extract v_5461 224 256);
      v_5600 <- eval (extract v_5470 224 256);
      setRegister (lhs.of_reg v_2681) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5462 0 1)) (uvalueMInt (extract v_5462 1 9)) (uvalueMInt (extract v_5462 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5471 0 1)) (uvalueMInt (extract v_5471 1 9)) (uvalueMInt (extract v_5471 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5481 0 1)) (uvalueMInt (extract v_5481 1 9)) (uvalueMInt (extract v_5481 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5489 0 1)) (uvalueMInt (extract v_5489 1 9)) (uvalueMInt (extract v_5489 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5500 0 1)) (uvalueMInt (extract v_5500 1 9)) (uvalueMInt (extract v_5500 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5508 0 1)) (uvalueMInt (extract v_5508 1 9)) (uvalueMInt (extract v_5508 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5518 0 1)) (uvalueMInt (extract v_5518 1 9)) (uvalueMInt (extract v_5518 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5526 0 1)) (uvalueMInt (extract v_5526 1 9)) (uvalueMInt (extract v_5526 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5537 0 1)) (uvalueMInt (extract v_5537 1 9)) (uvalueMInt (extract v_5537 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5545 0 1)) (uvalueMInt (extract v_5545 1 9)) (uvalueMInt (extract v_5545 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5555 0 1)) (uvalueMInt (extract v_5555 1 9)) (uvalueMInt (extract v_5555 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5563 0 1)) (uvalueMInt (extract v_5563 1 9)) (uvalueMInt (extract v_5563 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5574 0 1)) (uvalueMInt (extract v_5574 1 9)) (uvalueMInt (extract v_5574 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5582 0 1)) (uvalueMInt (extract v_5582 1 9)) (uvalueMInt (extract v_5582 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5592 0 1)) (uvalueMInt (extract v_5592 1 9)) (uvalueMInt (extract v_5592 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5600 0 1)) (uvalueMInt (extract v_5600 1 9)) (uvalueMInt (extract v_5600 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2663 : Mem) (v_2666 : reg (bv 128)) (v_2667 : reg (bv 128)) => do
      v_10896 <- getRegister v_2666;
      v_10897 <- eval (extract v_10896 0 32);
      v_10905 <- evaluateAddress v_2663;
      v_10906 <- load v_10905 16;
      v_10907 <- eval (extract v_10906 0 32);
      v_10917 <- eval (extract v_10896 32 64);
      v_10925 <- eval (extract v_10906 32 64);
      v_10936 <- eval (extract v_10896 64 96);
      v_10944 <- eval (extract v_10906 64 96);
      v_10954 <- eval (extract v_10896 96 128);
      v_10962 <- eval (extract v_10906 96 128);
      setRegister (lhs.of_reg v_2667) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10897 0 1)) (uvalueMInt (extract v_10897 1 9)) (uvalueMInt (extract v_10897 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10907 0 1)) (uvalueMInt (extract v_10907 1 9)) (uvalueMInt (extract v_10907 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10917 0 1)) (uvalueMInt (extract v_10917 1 9)) (uvalueMInt (extract v_10917 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10925 0 1)) (uvalueMInt (extract v_10925 1 9)) (uvalueMInt (extract v_10925 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10936 0 1)) (uvalueMInt (extract v_10936 1 9)) (uvalueMInt (extract v_10936 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10944 0 1)) (uvalueMInt (extract v_10944 1 9)) (uvalueMInt (extract v_10944 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10954 0 1)) (uvalueMInt (extract v_10954 1 9)) (uvalueMInt (extract v_10954 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10962 0 1)) (uvalueMInt (extract v_10962 1 9)) (uvalueMInt (extract v_10962 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2674 : Mem) (v_2675 : reg (bv 256)) (v_2676 : reg (bv 256)) => do
      v_10975 <- getRegister v_2675;
      v_10976 <- eval (extract v_10975 0 32);
      v_10984 <- evaluateAddress v_2674;
      v_10985 <- load v_10984 32;
      v_10986 <- eval (extract v_10985 0 32);
      v_10996 <- eval (extract v_10975 32 64);
      v_11004 <- eval (extract v_10985 32 64);
      v_11015 <- eval (extract v_10975 64 96);
      v_11023 <- eval (extract v_10985 64 96);
      v_11033 <- eval (extract v_10975 96 128);
      v_11041 <- eval (extract v_10985 96 128);
      v_11052 <- eval (extract v_10975 128 160);
      v_11060 <- eval (extract v_10985 128 160);
      v_11070 <- eval (extract v_10975 160 192);
      v_11078 <- eval (extract v_10985 160 192);
      v_11089 <- eval (extract v_10975 192 224);
      v_11097 <- eval (extract v_10985 192 224);
      v_11107 <- eval (extract v_10975 224 256);
      v_11115 <- eval (extract v_10985 224 256);
      setRegister (lhs.of_reg v_2676) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10976 0 1)) (uvalueMInt (extract v_10976 1 9)) (uvalueMInt (extract v_10976 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10986 0 1)) (uvalueMInt (extract v_10986 1 9)) (uvalueMInt (extract v_10986 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10996 0 1)) (uvalueMInt (extract v_10996 1 9)) (uvalueMInt (extract v_10996 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11004 0 1)) (uvalueMInt (extract v_11004 1 9)) (uvalueMInt (extract v_11004 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11015 0 1)) (uvalueMInt (extract v_11015 1 9)) (uvalueMInt (extract v_11015 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11023 0 1)) (uvalueMInt (extract v_11023 1 9)) (uvalueMInt (extract v_11023 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11033 0 1)) (uvalueMInt (extract v_11033 1 9)) (uvalueMInt (extract v_11033 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11041 0 1)) (uvalueMInt (extract v_11041 1 9)) (uvalueMInt (extract v_11041 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11052 0 1)) (uvalueMInt (extract v_11052 1 9)) (uvalueMInt (extract v_11052 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11060 0 1)) (uvalueMInt (extract v_11060 1 9)) (uvalueMInt (extract v_11060 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11070 0 1)) (uvalueMInt (extract v_11070 1 9)) (uvalueMInt (extract v_11070 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11078 0 1)) (uvalueMInt (extract v_11078 1 9)) (uvalueMInt (extract v_11078 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11089 0 1)) (uvalueMInt (extract v_11089 1 9)) (uvalueMInt (extract v_11089 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11097 0 1)) (uvalueMInt (extract v_11097 1 9)) (uvalueMInt (extract v_11097 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11107 0 1)) (uvalueMInt (extract v_11107 1 9)) (uvalueMInt (extract v_11107 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11115 0 1)) (uvalueMInt (extract v_11115 1 9)) (uvalueMInt (extract v_11115 9 32)))) 32)))));
      pure ()
    pat_end
