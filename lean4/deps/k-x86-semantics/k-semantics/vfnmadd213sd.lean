def vfnmadd213sd1 : instruction :=
  definst "vfnmadd213sd" $ do
    pattern fun (v_3277 : reg (bv 128)) (v_3278 : reg (bv 128)) (v_3279 : reg (bv 128)) => do
      v_7147 <- getRegister v_3279;
      v_7150 <- getRegister v_3278;
      v_7152 <- getRegister v_3277;
      setRegister (lhs.of_reg v_3279) (concat (extract v_7147 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_7147 64 128) (extract v_7150 64 128) (extract v_7152 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3274 : Mem) (v_3272 : reg (bv 128)) (v_3273 : reg (bv 128)) => do
      v_12887 <- getRegister v_3273;
      v_12890 <- getRegister v_3272;
      v_12892 <- evaluateAddress v_3274;
      v_12893 <- load v_12892 8;
      setRegister (lhs.of_reg v_3273) (concat (extract v_12887 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_12887 64 128) (extract v_12890 64 128) v_12893));
      pure ()
    pat_end
