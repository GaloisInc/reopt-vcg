def vaddpd1 : instruction :=
  definst "vaddpd" $ do
    pattern fun (v_2583 : reg (bv 128)) (v_2584 : reg (bv 128)) (v_2585 : reg (bv 128)) => do
      v_4824 <- getRegister v_2584;
      v_4825 <- eval (extract v_4824 0 64);
      v_4833 <- getRegister v_2583;
      v_4834 <- eval (extract v_4833 0 64);
      v_4844 <- eval (extract v_4824 64 128);
      v_4852 <- eval (extract v_4833 64 128);
      setRegister (lhs.of_reg v_2585) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4825 0 1)) (uvalueMInt (extract v_4825 1 12)) (uvalueMInt (extract v_4825 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4834 0 1)) (uvalueMInt (extract v_4834 1 12)) (uvalueMInt (extract v_4834 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4844 0 1)) (uvalueMInt (extract v_4844 1 12)) (uvalueMInt (extract v_4844 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4852 0 1)) (uvalueMInt (extract v_4852 1 12)) (uvalueMInt (extract v_4852 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2591 : reg (bv 256)) (v_2592 : reg (bv 256)) (v_2593 : reg (bv 256)) => do
      v_4869 <- getRegister v_2592;
      v_4870 <- eval (extract v_4869 0 64);
      v_4878 <- getRegister v_2591;
      v_4879 <- eval (extract v_4878 0 64);
      v_4889 <- eval (extract v_4869 64 128);
      v_4897 <- eval (extract v_4878 64 128);
      v_4907 <- eval (extract v_4869 128 192);
      v_4915 <- eval (extract v_4878 128 192);
      v_4925 <- eval (extract v_4869 192 256);
      v_4933 <- eval (extract v_4878 192 256);
      setRegister (lhs.of_reg v_2593) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4870 0 1)) (uvalueMInt (extract v_4870 1 12)) (uvalueMInt (extract v_4870 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4879 0 1)) (uvalueMInt (extract v_4879 1 12)) (uvalueMInt (extract v_4879 12 64)))) 64) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4889 0 1)) (uvalueMInt (extract v_4889 1 12)) (uvalueMInt (extract v_4889 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4897 0 1)) (uvalueMInt (extract v_4897 1 12)) (uvalueMInt (extract v_4897 12 64)))) 64) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4907 0 1)) (uvalueMInt (extract v_4907 1 12)) (uvalueMInt (extract v_4907 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4915 0 1)) (uvalueMInt (extract v_4915 1 12)) (uvalueMInt (extract v_4915 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4925 0 1)) (uvalueMInt (extract v_4925 1 12)) (uvalueMInt (extract v_4925 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4933 0 1)) (uvalueMInt (extract v_4933 1 12)) (uvalueMInt (extract v_4933 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_2575 : Mem) (v_2578 : reg (bv 128)) (v_2579 : reg (bv 128)) => do
      v_10376 <- getRegister v_2578;
      v_10377 <- eval (extract v_10376 0 64);
      v_10385 <- evaluateAddress v_2575;
      v_10386 <- load v_10385 16;
      v_10387 <- eval (extract v_10386 0 64);
      v_10397 <- eval (extract v_10376 64 128);
      v_10405 <- eval (extract v_10386 64 128);
      setRegister (lhs.of_reg v_2579) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10377 0 1)) (uvalueMInt (extract v_10377 1 12)) (uvalueMInt (extract v_10377 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10387 0 1)) (uvalueMInt (extract v_10387 1 12)) (uvalueMInt (extract v_10387 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10397 0 1)) (uvalueMInt (extract v_10397 1 12)) (uvalueMInt (extract v_10397 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10405 0 1)) (uvalueMInt (extract v_10405 1 12)) (uvalueMInt (extract v_10405 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2586 : Mem) (v_2587 : reg (bv 256)) (v_2588 : reg (bv 256)) => do
      v_10417 <- getRegister v_2587;
      v_10418 <- eval (extract v_10417 0 64);
      v_10426 <- evaluateAddress v_2586;
      v_10427 <- load v_10426 32;
      v_10428 <- eval (extract v_10427 0 64);
      v_10438 <- eval (extract v_10417 64 128);
      v_10446 <- eval (extract v_10427 64 128);
      v_10456 <- eval (extract v_10417 128 192);
      v_10464 <- eval (extract v_10427 128 192);
      v_10474 <- eval (extract v_10417 192 256);
      v_10482 <- eval (extract v_10427 192 256);
      setRegister (lhs.of_reg v_2588) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10418 0 1)) (uvalueMInt (extract v_10418 1 12)) (uvalueMInt (extract v_10418 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10428 0 1)) (uvalueMInt (extract v_10428 1 12)) (uvalueMInt (extract v_10428 12 64)))) 64) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10438 0 1)) (uvalueMInt (extract v_10438 1 12)) (uvalueMInt (extract v_10438 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10446 0 1)) (uvalueMInt (extract v_10446 1 12)) (uvalueMInt (extract v_10446 12 64)))) 64) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10456 0 1)) (uvalueMInt (extract v_10456 1 12)) (uvalueMInt (extract v_10456 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10464 0 1)) (uvalueMInt (extract v_10464 1 12)) (uvalueMInt (extract v_10464 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10474 0 1)) (uvalueMInt (extract v_10474 1 12)) (uvalueMInt (extract v_10474 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10482 0 1)) (uvalueMInt (extract v_10482 1 12)) (uvalueMInt (extract v_10482 12 64)))) 64))));
      pure ()
    pat_end
