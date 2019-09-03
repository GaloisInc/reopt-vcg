def vfmsubadd231pd1 : instruction :=
  definst "vfmsubadd231pd" $ do
    pattern fun (v_3047 : reg (bv 128)) (v_3048 : reg (bv 128)) (v_3049 : reg (bv 128)) => do
      v_10012 <- getRegister v_3048;
      v_10013 <- eval (extract v_10012 0 64);
      v_10021 <- getRegister v_3047;
      v_10022 <- eval (extract v_10021 0 64);
      v_10031 <- getRegister v_3049;
      v_10032 <- eval (extract v_10031 0 64);
      v_10042 <- eval (extract v_10012 64 128);
      v_10050 <- eval (extract v_10021 64 128);
      v_10059 <- eval (extract v_10031 64 128);
      setRegister (lhs.of_reg v_3049) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10013 0 1)) (uvalueMInt (extract v_10013 1 12)) (uvalueMInt (extract v_10013 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10022 0 1)) (uvalueMInt (extract v_10022 1 12)) (uvalueMInt (extract v_10022 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10032 0 1)) (uvalueMInt (extract v_10032 1 12)) (uvalueMInt (extract v_10032 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10042 0 1)) (uvalueMInt (extract v_10042 1 12)) (uvalueMInt (extract v_10042 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10050 0 1)) (uvalueMInt (extract v_10050 1 12)) (uvalueMInt (extract v_10050 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10059 0 1)) (uvalueMInt (extract v_10059 1 12)) (uvalueMInt (extract v_10059 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3058 : reg (bv 256)) (v_3059 : reg (bv 256)) (v_3060 : reg (bv 256)) => do
      v_10076 <- getRegister v_3059;
      v_10077 <- eval (extract v_10076 0 64);
      v_10085 <- getRegister v_3058;
      v_10086 <- eval (extract v_10085 0 64);
      v_10095 <- getRegister v_3060;
      v_10096 <- eval (extract v_10095 0 64);
      v_10106 <- eval (extract v_10076 64 128);
      v_10114 <- eval (extract v_10085 64 128);
      v_10123 <- eval (extract v_10095 64 128);
      v_10134 <- eval (extract v_10076 128 192);
      v_10142 <- eval (extract v_10085 128 192);
      v_10151 <- eval (extract v_10095 128 192);
      v_10161 <- eval (extract v_10076 192 256);
      v_10169 <- eval (extract v_10085 192 256);
      v_10178 <- eval (extract v_10095 192 256);
      setRegister (lhs.of_reg v_3060) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10077 0 1)) (uvalueMInt (extract v_10077 1 12)) (uvalueMInt (extract v_10077 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10086 0 1)) (uvalueMInt (extract v_10086 1 12)) (uvalueMInt (extract v_10086 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10096 0 1)) (uvalueMInt (extract v_10096 1 12)) (uvalueMInt (extract v_10096 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10106 0 1)) (uvalueMInt (extract v_10106 1 12)) (uvalueMInt (extract v_10106 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10114 0 1)) (uvalueMInt (extract v_10114 1 12)) (uvalueMInt (extract v_10114 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10123 0 1)) (uvalueMInt (extract v_10123 1 12)) (uvalueMInt (extract v_10123 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10134 0 1)) (uvalueMInt (extract v_10134 1 12)) (uvalueMInt (extract v_10134 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10142 0 1)) (uvalueMInt (extract v_10142 1 12)) (uvalueMInt (extract v_10142 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10151 0 1)) (uvalueMInt (extract v_10151 1 12)) (uvalueMInt (extract v_10151 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10161 0 1)) (uvalueMInt (extract v_10161 1 12)) (uvalueMInt (extract v_10161 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10169 0 1)) (uvalueMInt (extract v_10169 1 12)) (uvalueMInt (extract v_10169 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10178 0 1)) (uvalueMInt (extract v_10178 1 12)) (uvalueMInt (extract v_10178 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_3044 : Mem) (v_3042 : reg (bv 128)) (v_3043 : reg (bv 128)) => do
      v_20725 <- getRegister v_3042;
      v_20726 <- eval (extract v_20725 0 64);
      v_20734 <- evaluateAddress v_3044;
      v_20735 <- load v_20734 16;
      v_20736 <- eval (extract v_20735 0 64);
      v_20745 <- getRegister v_3043;
      v_20746 <- eval (extract v_20745 0 64);
      v_20756 <- eval (extract v_20725 64 128);
      v_20764 <- eval (extract v_20735 64 128);
      v_20773 <- eval (extract v_20745 64 128);
      setRegister (lhs.of_reg v_3043) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20726 0 1)) (uvalueMInt (extract v_20726 1 12)) (uvalueMInt (extract v_20726 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20736 0 1)) (uvalueMInt (extract v_20736 1 12)) (uvalueMInt (extract v_20736 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20746 0 1)) (uvalueMInt (extract v_20746 1 12)) (uvalueMInt (extract v_20746 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20756 0 1)) (uvalueMInt (extract v_20756 1 12)) (uvalueMInt (extract v_20756 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20764 0 1)) (uvalueMInt (extract v_20764 1 12)) (uvalueMInt (extract v_20764 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20773 0 1)) (uvalueMInt (extract v_20773 1 12)) (uvalueMInt (extract v_20773 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3053 : Mem) (v_3054 : reg (bv 256)) (v_3055 : reg (bv 256)) => do
      v_20785 <- getRegister v_3054;
      v_20786 <- eval (extract v_20785 0 64);
      v_20794 <- evaluateAddress v_3053;
      v_20795 <- load v_20794 32;
      v_20796 <- eval (extract v_20795 0 64);
      v_20805 <- getRegister v_3055;
      v_20806 <- eval (extract v_20805 0 64);
      v_20816 <- eval (extract v_20785 64 128);
      v_20824 <- eval (extract v_20795 64 128);
      v_20833 <- eval (extract v_20805 64 128);
      v_20844 <- eval (extract v_20785 128 192);
      v_20852 <- eval (extract v_20795 128 192);
      v_20861 <- eval (extract v_20805 128 192);
      v_20871 <- eval (extract v_20785 192 256);
      v_20879 <- eval (extract v_20795 192 256);
      v_20888 <- eval (extract v_20805 192 256);
      setRegister (lhs.of_reg v_3055) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20786 0 1)) (uvalueMInt (extract v_20786 1 12)) (uvalueMInt (extract v_20786 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20796 0 1)) (uvalueMInt (extract v_20796 1 12)) (uvalueMInt (extract v_20796 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20806 0 1)) (uvalueMInt (extract v_20806 1 12)) (uvalueMInt (extract v_20806 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20816 0 1)) (uvalueMInt (extract v_20816 1 12)) (uvalueMInt (extract v_20816 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20824 0 1)) (uvalueMInt (extract v_20824 1 12)) (uvalueMInt (extract v_20824 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20833 0 1)) (uvalueMInt (extract v_20833 1 12)) (uvalueMInt (extract v_20833 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20844 0 1)) (uvalueMInt (extract v_20844 1 12)) (uvalueMInt (extract v_20844 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20852 0 1)) (uvalueMInt (extract v_20852 1 12)) (uvalueMInt (extract v_20852 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20861 0 1)) (uvalueMInt (extract v_20861 1 12)) (uvalueMInt (extract v_20861 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20871 0 1)) (uvalueMInt (extract v_20871 1 12)) (uvalueMInt (extract v_20871 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20879 0 1)) (uvalueMInt (extract v_20879 1 12)) (uvalueMInt (extract v_20879 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20888 0 1)) (uvalueMInt (extract v_20888 1 12)) (uvalueMInt (extract v_20888 12 64)))) 64)));
      pure ()
    pat_end
