def vfnmadd132sd1 : instruction :=
  definst "vfnmadd132sd" $ do
    pattern fun (v_3187 : reg (bv 128)) (v_3188 : reg (bv 128)) (v_3189 : reg (bv 128)) => do
      v_6963 <- getRegister v_3189;
      v_6966 <- getRegister v_3188;
      v_6968 <- getRegister v_3187;
      setRegister (lhs.of_reg v_3189) (concat (extract v_6963 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6963 64 128) (extract v_6966 64 128) (extract v_6968 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3181 : Mem) (v_3182 : reg (bv 128)) (v_3183 : reg (bv 128)) => do
      v_12729 <- getRegister v_3183;
      v_12732 <- getRegister v_3182;
      v_12734 <- evaluateAddress v_3181;
      v_12735 <- load v_12734 8;
      setRegister (lhs.of_reg v_3183) (concat (extract v_12729 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12729 64 128) (extract v_12732 64 128) v_12735));
      pure ()
    pat_end
