def vfnmsub132pd1 : instruction :=
  definst "vfnmsub132pd" $ do
    pattern fun (v_3289 : reg (bv 128)) (v_3290 : reg (bv 128)) (v_3291 : reg (bv 128)) => do
      v_11033 <- getRegister v_3291;
      v_11034 <- eval (extract v_11033 0 64);
      v_11042 <- getRegister v_3289;
      v_11043 <- eval (extract v_11042 0 64);
      v_11053 <- getRegister v_3290;
      v_11054 <- eval (extract v_11053 0 64);
      v_11064 <- eval (extract v_11033 64 128);
      v_11072 <- eval (extract v_11042 64 128);
      v_11082 <- eval (extract v_11053 64 128);
      setRegister (lhs.of_reg v_3291) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11034 0 1)) (uvalueMInt (extract v_11034 1 12)) (uvalueMInt (extract v_11034 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11043 0 1)) (uvalueMInt (extract v_11043 1 12)) (uvalueMInt (extract v_11043 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11054 0 1)) (uvalueMInt (extract v_11054 1 12)) (uvalueMInt (extract v_11054 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11064 0 1)) (uvalueMInt (extract v_11064 1 12)) (uvalueMInt (extract v_11064 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11072 0 1)) (uvalueMInt (extract v_11072 1 12)) (uvalueMInt (extract v_11072 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11082 0 1)) (uvalueMInt (extract v_11082 1 12)) (uvalueMInt (extract v_11082 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3300 : reg (bv 256)) (v_3301 : reg (bv 256)) (v_3302 : reg (bv 256)) => do
      v_11099 <- getRegister v_3302;
      v_11100 <- eval (extract v_11099 0 64);
      v_11108 <- getRegister v_3300;
      v_11109 <- eval (extract v_11108 0 64);
      v_11119 <- getRegister v_3301;
      v_11120 <- eval (extract v_11119 0 64);
      v_11130 <- eval (extract v_11099 64 128);
      v_11138 <- eval (extract v_11108 64 128);
      v_11148 <- eval (extract v_11119 64 128);
      v_11158 <- eval (extract v_11099 128 192);
      v_11166 <- eval (extract v_11108 128 192);
      v_11176 <- eval (extract v_11119 128 192);
      v_11186 <- eval (extract v_11099 192 256);
      v_11194 <- eval (extract v_11108 192 256);
      v_11204 <- eval (extract v_11119 192 256);
      setRegister (lhs.of_reg v_3302) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11100 0 1)) (uvalueMInt (extract v_11100 1 12)) (uvalueMInt (extract v_11100 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11109 0 1)) (uvalueMInt (extract v_11109 1 12)) (uvalueMInt (extract v_11109 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11120 0 1)) (uvalueMInt (extract v_11120 1 12)) (uvalueMInt (extract v_11120 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11130 0 1)) (uvalueMInt (extract v_11130 1 12)) (uvalueMInt (extract v_11130 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11138 0 1)) (uvalueMInt (extract v_11138 1 12)) (uvalueMInt (extract v_11138 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11148 0 1)) (uvalueMInt (extract v_11148 1 12)) (uvalueMInt (extract v_11148 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11158 0 1)) (uvalueMInt (extract v_11158 1 12)) (uvalueMInt (extract v_11158 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11166 0 1)) (uvalueMInt (extract v_11166 1 12)) (uvalueMInt (extract v_11166 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11176 0 1)) (uvalueMInt (extract v_11176 1 12)) (uvalueMInt (extract v_11176 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11186 0 1)) (uvalueMInt (extract v_11186 1 12)) (uvalueMInt (extract v_11186 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11194 0 1)) (uvalueMInt (extract v_11194 1 12)) (uvalueMInt (extract v_11194 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11204 0 1)) (uvalueMInt (extract v_11204 1 12)) (uvalueMInt (extract v_11204 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_3286 : Mem) (v_3284 : reg (bv 128)) (v_3285 : reg (bv 128)) => do
      v_21652 <- getRegister v_3285;
      v_21653 <- eval (extract v_21652 0 64);
      v_21661 <- evaluateAddress v_3286;
      v_21662 <- load v_21661 16;
      v_21663 <- eval (extract v_21662 0 64);
      v_21673 <- getRegister v_3284;
      v_21674 <- eval (extract v_21673 0 64);
      v_21684 <- eval (extract v_21652 64 128);
      v_21692 <- eval (extract v_21662 64 128);
      v_21702 <- eval (extract v_21673 64 128);
      setRegister (lhs.of_reg v_3285) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21653 0 1)) (uvalueMInt (extract v_21653 1 12)) (uvalueMInt (extract v_21653 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21663 0 1)) (uvalueMInt (extract v_21663 1 12)) (uvalueMInt (extract v_21663 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21674 0 1)) (uvalueMInt (extract v_21674 1 12)) (uvalueMInt (extract v_21674 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21684 0 1)) (uvalueMInt (extract v_21684 1 12)) (uvalueMInt (extract v_21684 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21692 0 1)) (uvalueMInt (extract v_21692 1 12)) (uvalueMInt (extract v_21692 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21702 0 1)) (uvalueMInt (extract v_21702 1 12)) (uvalueMInt (extract v_21702 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3295 : Mem) (v_3296 : reg (bv 256)) (v_3297 : reg (bv 256)) => do
      v_21714 <- getRegister v_3297;
      v_21715 <- eval (extract v_21714 0 64);
      v_21723 <- evaluateAddress v_3295;
      v_21724 <- load v_21723 32;
      v_21725 <- eval (extract v_21724 0 64);
      v_21735 <- getRegister v_3296;
      v_21736 <- eval (extract v_21735 0 64);
      v_21746 <- eval (extract v_21714 64 128);
      v_21754 <- eval (extract v_21724 64 128);
      v_21764 <- eval (extract v_21735 64 128);
      v_21774 <- eval (extract v_21714 128 192);
      v_21782 <- eval (extract v_21724 128 192);
      v_21792 <- eval (extract v_21735 128 192);
      v_21802 <- eval (extract v_21714 192 256);
      v_21810 <- eval (extract v_21724 192 256);
      v_21820 <- eval (extract v_21735 192 256);
      setRegister (lhs.of_reg v_3297) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21715 0 1)) (uvalueMInt (extract v_21715 1 12)) (uvalueMInt (extract v_21715 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21725 0 1)) (uvalueMInt (extract v_21725 1 12)) (uvalueMInt (extract v_21725 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21736 0 1)) (uvalueMInt (extract v_21736 1 12)) (uvalueMInt (extract v_21736 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21746 0 1)) (uvalueMInt (extract v_21746 1 12)) (uvalueMInt (extract v_21746 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21754 0 1)) (uvalueMInt (extract v_21754 1 12)) (uvalueMInt (extract v_21754 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21764 0 1)) (uvalueMInt (extract v_21764 1 12)) (uvalueMInt (extract v_21764 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21774 0 1)) (uvalueMInt (extract v_21774 1 12)) (uvalueMInt (extract v_21774 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21782 0 1)) (uvalueMInt (extract v_21782 1 12)) (uvalueMInt (extract v_21782 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21792 0 1)) (uvalueMInt (extract v_21792 1 12)) (uvalueMInt (extract v_21792 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21802 0 1)) (uvalueMInt (extract v_21802 1 12)) (uvalueMInt (extract v_21802 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21810 0 1)) (uvalueMInt (extract v_21810 1 12)) (uvalueMInt (extract v_21810 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_21820 0 1)) (uvalueMInt (extract v_21820 1 12)) (uvalueMInt (extract v_21820 12 64)))) 64))));
      pure ()
    pat_end
