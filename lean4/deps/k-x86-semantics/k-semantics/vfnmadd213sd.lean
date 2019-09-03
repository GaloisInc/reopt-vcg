def vfnmadd213sd1 : instruction :=
  definst "vfnmadd213sd" $ do
    pattern fun (v_3188 : reg (bv 128)) (v_3189 : reg (bv 128)) (v_3190 : reg (bv 128)) => do
      v_7048 <- getRegister v_3190;
      v_7051 <- getRegister v_3189;
      v_7053 <- getRegister v_3188;
      setRegister (lhs.of_reg v_3190) (concat (extract v_7048 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_7048 64 128) (extract v_7051 64 128) (extract v_7053 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3185 : Mem) (v_3183 : reg (bv 128)) (v_3184 : reg (bv 128)) => do
      v_12771 <- getRegister v_3184;
      v_12774 <- getRegister v_3183;
      v_12776 <- evaluateAddress v_3185;
      v_12777 <- load v_12776 8;
      setRegister (lhs.of_reg v_3184) (concat (extract v_12771 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_12771 64 128) (extract v_12774 64 128) v_12777));
      pure ()
    pat_end
