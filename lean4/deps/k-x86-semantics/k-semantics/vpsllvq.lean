def vpsllvq1 : instruction :=
  definst "vpsllvq" $ do
    pattern fun (v_3206 : reg (bv 128)) (v_3207 : reg (bv 128)) (v_3208 : reg (bv 128)) => do
      v_7961 <- getRegister v_3207;
      v_7963 <- getRegister v_3206;
      setRegister (lhs.of_reg v_3208) (concat (extract (shl (extract v_7961 0 64) (extract v_7963 0 64)) 0 64) (extract (shl (extract v_7961 64 128) (extract v_7963 64 128)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_3217 : reg (bv 256)) (v_3218 : reg (bv 256)) (v_3219 : reg (bv 256)) => do
      v_7978 <- getRegister v_3218;
      v_7980 <- getRegister v_3217;
      setRegister (lhs.of_reg v_3219) (concat (extract (shl (extract v_7978 0 64) (extract v_7980 0 64)) 0 64) (concat (extract (shl (extract v_7978 64 128) (extract v_7980 64 128)) 0 64) (concat (extract (shl (extract v_7978 128 192) (extract v_7980 128 192)) 0 64) (extract (shl (extract v_7978 192 256) (extract v_7980 192 256)) 0 64))));
      pure ()
    pat_end;
    pattern fun (v_3200 : Mem) (v_3201 : reg (bv 128)) (v_3202 : reg (bv 128)) => do
      v_14092 <- getRegister v_3201;
      v_14094 <- evaluateAddress v_3200;
      v_14095 <- load v_14094 16;
      setRegister (lhs.of_reg v_3202) (concat (extract (shl (extract v_14092 0 64) (extract v_14095 0 64)) 0 64) (extract (shl (extract v_14092 64 128) (extract v_14095 64 128)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_3211 : Mem) (v_3212 : reg (bv 256)) (v_3213 : reg (bv 256)) => do
      v_14105 <- getRegister v_3212;
      v_14107 <- evaluateAddress v_3211;
      v_14108 <- load v_14107 32;
      setRegister (lhs.of_reg v_3213) (concat (extract (shl (extract v_14105 0 64) (extract v_14108 0 64)) 0 64) (concat (extract (shl (extract v_14105 64 128) (extract v_14108 64 128)) 0 64) (concat (extract (shl (extract v_14105 128 192) (extract v_14108 128 192)) 0 64) (extract (shl (extract v_14105 192 256) (extract v_14108 192 256)) 0 64))));
      pure ()
    pat_end
