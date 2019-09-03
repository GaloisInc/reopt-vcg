def vfmsubadd132pd1 : instruction :=
  definst "vfmsubadd132pd" $ do
    pattern fun (v_2959 : reg (bv 128)) (v_2960 : reg (bv 128)) (v_2961 : reg (bv 128)) => do
      v_9009 <- getRegister v_2961;
      v_9010 <- eval (extract v_9009 0 64);
      v_9018 <- getRegister v_2959;
      v_9019 <- eval (extract v_9018 0 64);
      v_9028 <- getRegister v_2960;
      v_9029 <- eval (extract v_9028 0 64);
      setRegister (lhs.of_reg v_2961) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9010 0 1)) (uvalueMInt (extract v_9010 1 12)) (uvalueMInt (extract v_9010 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9019 0 1)) (uvalueMInt (extract v_9019 1 12)) (uvalueMInt (extract v_9019 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9029 0 1)) (uvalueMInt (extract v_9029 1 12)) (uvalueMInt (extract v_9029 12 64)))) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_9009 64 128) (extract v_9028 64 128) (extract v_9018 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2970 : reg (bv 256)) (v_2971 : reg (bv 256)) (v_2972 : reg (bv 256)) => do
      v_9050 <- getRegister v_2972;
      v_9051 <- eval (extract v_9050 0 64);
      v_9059 <- getRegister v_2970;
      v_9060 <- eval (extract v_9059 0 64);
      v_9069 <- getRegister v_2971;
      v_9070 <- eval (extract v_9069 0 64);
      v_9085 <- eval (extract v_9050 128 192);
      v_9093 <- eval (extract v_9059 128 192);
      v_9102 <- eval (extract v_9069 128 192);
      setRegister (lhs.of_reg v_2972) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9051 0 1)) (uvalueMInt (extract v_9051 1 12)) (uvalueMInt (extract v_9051 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9060 0 1)) (uvalueMInt (extract v_9060 1 12)) (uvalueMInt (extract v_9060 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9070 0 1)) (uvalueMInt (extract v_9070 1 12)) (uvalueMInt (extract v_9070 12 64)))) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_9050 64 128) (extract v_9069 64 128) (extract v_9059 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9085 0 1)) (uvalueMInt (extract v_9085 1 12)) (uvalueMInt (extract v_9085 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9093 0 1)) (uvalueMInt (extract v_9093 1 12)) (uvalueMInt (extract v_9093 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9102 0 1)) (uvalueMInt (extract v_9102 1 12)) (uvalueMInt (extract v_9102 12 64)))) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_9050 192 256) (extract v_9069 192 256) (extract v_9059 192 256))));
      pure ()
    pat_end;
    pattern fun (v_2956 : Mem) (v_2954 : reg (bv 128)) (v_2955 : reg (bv 128)) => do
      v_19754 <- getRegister v_2955;
      v_19755 <- eval (extract v_19754 0 64);
      v_19763 <- evaluateAddress v_2956;
      v_19764 <- load v_19763 16;
      v_19765 <- eval (extract v_19764 0 64);
      v_19774 <- getRegister v_2954;
      v_19775 <- eval (extract v_19774 0 64);
      setRegister (lhs.of_reg v_2955) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19755 0 1)) (uvalueMInt (extract v_19755 1 12)) (uvalueMInt (extract v_19755 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19765 0 1)) (uvalueMInt (extract v_19765 1 12)) (uvalueMInt (extract v_19765 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19775 0 1)) (uvalueMInt (extract v_19775 1 12)) (uvalueMInt (extract v_19775 12 64)))) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_19754 64 128) (extract v_19774 64 128) (extract v_19764 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2965 : Mem) (v_2966 : reg (bv 256)) (v_2967 : reg (bv 256)) => do
      v_19791 <- getRegister v_2967;
      v_19792 <- eval (extract v_19791 0 64);
      v_19800 <- evaluateAddress v_2965;
      v_19801 <- load v_19800 32;
      v_19802 <- eval (extract v_19801 0 64);
      v_19811 <- getRegister v_2966;
      v_19812 <- eval (extract v_19811 0 64);
      v_19827 <- eval (extract v_19791 128 192);
      v_19835 <- eval (extract v_19801 128 192);
      v_19844 <- eval (extract v_19811 128 192);
      setRegister (lhs.of_reg v_2967) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19792 0 1)) (uvalueMInt (extract v_19792 1 12)) (uvalueMInt (extract v_19792 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19802 0 1)) (uvalueMInt (extract v_19802 1 12)) (uvalueMInt (extract v_19802 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19812 0 1)) (uvalueMInt (extract v_19812 1 12)) (uvalueMInt (extract v_19812 12 64)))) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_19791 64 128) (extract v_19811 64 128) (extract v_19801 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19827 0 1)) (uvalueMInt (extract v_19827 1 12)) (uvalueMInt (extract v_19827 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19835 0 1)) (uvalueMInt (extract v_19835 1 12)) (uvalueMInt (extract v_19835 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19844 0 1)) (uvalueMInt (extract v_19844 1 12)) (uvalueMInt (extract v_19844 12 64)))) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_19791 192 256) (extract v_19811 192 256) (extract v_19801 192 256))));
      pure ()
    pat_end
