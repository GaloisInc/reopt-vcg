def vfmsubadd132pd1 : instruction :=
  definst "vfmsubadd132pd" $ do
    pattern fun (v_2946 : reg (bv 128)) (v_2947 : reg (bv 128)) (v_2948 : reg (bv 128)) => do
      v_6153 <- getRegister v_2948;
      v_6156 <- getRegister v_2946;
      v_6160 <- getRegister v_2947;
      setRegister (lhs.of_reg v_2948) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6153 0 64) 53 11) (MInt2Float (extract v_6156 0 64) 53 11)) (MInt2Float (extract v_6160 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6153 64 128) (extract v_6160 64 128) (extract v_6156 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2958 : reg (bv 256)) (v_2959 : reg (bv 256)) (v_2960 : reg (bv 256)) => do
      v_6176 <- getRegister v_2960;
      v_6179 <- getRegister v_2958;
      v_6183 <- getRegister v_2959;
      setRegister (lhs.of_reg v_2960) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6176 0 64) 53 11) (MInt2Float (extract v_6179 0 64) 53 11)) (MInt2Float (extract v_6183 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6176 64 128) (extract v_6183 64 128) (extract v_6179 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6176 128 192) 53 11) (MInt2Float (extract v_6179 128 192) 53 11)) (MInt2Float (extract v_6183 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6176 192 256) (extract v_6183 192 256) (extract v_6179 192 256))));
      pure ()
    pat_end;
    pattern fun (v_2943 : Mem) (v_2941 : reg (bv 128)) (v_2942 : reg (bv 128)) => do
      v_11966 <- getRegister v_2942;
      v_11969 <- evaluateAddress v_2943;
      v_11970 <- load v_11969 16;
      v_11974 <- getRegister v_2941;
      setRegister (lhs.of_reg v_2942) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11966 0 64) 53 11) (MInt2Float (extract v_11970 0 64) 53 11)) (MInt2Float (extract v_11974 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_11966 64 128) (extract v_11974 64 128) (extract v_11970 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2952 : Mem) (v_2953 : reg (bv 256)) (v_2954 : reg (bv 256)) => do
      v_11985 <- getRegister v_2954;
      v_11988 <- evaluateAddress v_2952;
      v_11989 <- load v_11988 32;
      v_11993 <- getRegister v_2953;
      setRegister (lhs.of_reg v_2954) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11985 0 64) 53 11) (MInt2Float (extract v_11989 0 64) 53 11)) (MInt2Float (extract v_11993 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_11985 64 128) (extract v_11993 64 128) (extract v_11989 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11985 128 192) 53 11) (MInt2Float (extract v_11989 128 192) 53 11)) (MInt2Float (extract v_11993 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_11985 192 256) (extract v_11993 192 256) (extract v_11989 192 256))));
      pure ()
    pat_end
