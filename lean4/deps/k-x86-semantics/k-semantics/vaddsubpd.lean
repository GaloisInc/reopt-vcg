def vaddsubpd1 : instruction :=
  definst "vaddsubpd" $ do
    pattern fun (v_2649 : reg (bv 128)) (v_2650 : reg (bv 128)) (v_2651 : reg (bv 128)) => do
      v_5250 <- getRegister v_2650;
      v_5251 <- eval (extract v_5250 0 64);
      v_5259 <- getRegister v_2649;
      v_5260 <- eval (extract v_5259 0 64);
      v_5270 <- eval (extract v_5250 64 128);
      v_5278 <- eval (extract v_5259 64 128);
      setRegister (lhs.of_reg v_2651) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5251 0 1)) (uvalueMInt (extract v_5251 1 12)) (uvalueMInt (extract v_5251 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5260 0 1)) (uvalueMInt (extract v_5260 1 12)) (uvalueMInt (extract v_5260 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5270 0 1)) (uvalueMInt (extract v_5270 1 12)) (uvalueMInt (extract v_5270 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5278 0 1)) (uvalueMInt (extract v_5278 1 12)) (uvalueMInt (extract v_5278 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2657 : reg (bv 256)) (v_2658 : reg (bv 256)) (v_2659 : reg (bv 256)) => do
      v_5295 <- getRegister v_2658;
      v_5296 <- eval (extract v_5295 0 64);
      v_5304 <- getRegister v_2657;
      v_5305 <- eval (extract v_5304 0 64);
      v_5315 <- eval (extract v_5295 64 128);
      v_5323 <- eval (extract v_5304 64 128);
      v_5334 <- eval (extract v_5295 128 192);
      v_5342 <- eval (extract v_5304 128 192);
      v_5352 <- eval (extract v_5295 192 256);
      v_5360 <- eval (extract v_5304 192 256);
      setRegister (lhs.of_reg v_2659) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5296 0 1)) (uvalueMInt (extract v_5296 1 12)) (uvalueMInt (extract v_5296 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5305 0 1)) (uvalueMInt (extract v_5305 1 12)) (uvalueMInt (extract v_5305 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5315 0 1)) (uvalueMInt (extract v_5315 1 12)) (uvalueMInt (extract v_5315 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5323 0 1)) (uvalueMInt (extract v_5323 1 12)) (uvalueMInt (extract v_5323 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5334 0 1)) (uvalueMInt (extract v_5334 1 12)) (uvalueMInt (extract v_5334 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5342 0 1)) (uvalueMInt (extract v_5342 1 12)) (uvalueMInt (extract v_5342 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5352 0 1)) (uvalueMInt (extract v_5352 1 12)) (uvalueMInt (extract v_5352 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5360 0 1)) (uvalueMInt (extract v_5360 1 12)) (uvalueMInt (extract v_5360 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_2641 : Mem) (v_2644 : reg (bv 128)) (v_2645 : reg (bv 128)) => do
      v_10776 <- getRegister v_2644;
      v_10777 <- eval (extract v_10776 0 64);
      v_10785 <- evaluateAddress v_2641;
      v_10786 <- load v_10785 16;
      v_10787 <- eval (extract v_10786 0 64);
      v_10797 <- eval (extract v_10776 64 128);
      v_10805 <- eval (extract v_10786 64 128);
      setRegister (lhs.of_reg v_2645) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10777 0 1)) (uvalueMInt (extract v_10777 1 12)) (uvalueMInt (extract v_10777 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10787 0 1)) (uvalueMInt (extract v_10787 1 12)) (uvalueMInt (extract v_10787 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10797 0 1)) (uvalueMInt (extract v_10797 1 12)) (uvalueMInt (extract v_10797 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10805 0 1)) (uvalueMInt (extract v_10805 1 12)) (uvalueMInt (extract v_10805 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2652 : Mem) (v_2653 : reg (bv 256)) (v_2654 : reg (bv 256)) => do
      v_10817 <- getRegister v_2653;
      v_10818 <- eval (extract v_10817 0 64);
      v_10826 <- evaluateAddress v_2652;
      v_10827 <- load v_10826 32;
      v_10828 <- eval (extract v_10827 0 64);
      v_10838 <- eval (extract v_10817 64 128);
      v_10846 <- eval (extract v_10827 64 128);
      v_10857 <- eval (extract v_10817 128 192);
      v_10865 <- eval (extract v_10827 128 192);
      v_10875 <- eval (extract v_10817 192 256);
      v_10883 <- eval (extract v_10827 192 256);
      setRegister (lhs.of_reg v_2654) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10818 0 1)) (uvalueMInt (extract v_10818 1 12)) (uvalueMInt (extract v_10818 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10828 0 1)) (uvalueMInt (extract v_10828 1 12)) (uvalueMInt (extract v_10828 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10838 0 1)) (uvalueMInt (extract v_10838 1 12)) (uvalueMInt (extract v_10838 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10846 0 1)) (uvalueMInt (extract v_10846 1 12)) (uvalueMInt (extract v_10846 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10857 0 1)) (uvalueMInt (extract v_10857 1 12)) (uvalueMInt (extract v_10857 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10865 0 1)) (uvalueMInt (extract v_10865 1 12)) (uvalueMInt (extract v_10865 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10875 0 1)) (uvalueMInt (extract v_10875 1 12)) (uvalueMInt (extract v_10875 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10883 0 1)) (uvalueMInt (extract v_10883 1 12)) (uvalueMInt (extract v_10883 12 64)))) 64)));
      pure ()
    pat_end
