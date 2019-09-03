def vpsllvq1 : instruction :=
  definst "vpsllvq" $ do
    pattern fun (v_3153 : reg (bv 128)) (v_3154 : reg (bv 128)) (v_3155 : reg (bv 128)) => do
      v_7934 <- getRegister v_3154;
      v_7936 <- getRegister v_3153;
      setRegister (lhs.of_reg v_3155) (concat (extract (shl (extract v_7934 0 64) (uvalueMInt (extract v_7936 0 64))) 0 64) (extract (shl (extract v_7934 64 128) (uvalueMInt (extract v_7936 64 128))) 0 64));
      pure ()
    pat_end;
    pattern fun (v_3165 : reg (bv 256)) (v_3166 : reg (bv 256)) (v_3167 : reg (bv 256)) => do
      v_7953 <- getRegister v_3166;
      v_7955 <- getRegister v_3165;
      setRegister (lhs.of_reg v_3167) (concat (extract (shl (extract v_7953 0 64) (uvalueMInt (extract v_7955 0 64))) 0 64) (concat (extract (shl (extract v_7953 64 128) (uvalueMInt (extract v_7955 64 128))) 0 64) (concat (extract (shl (extract v_7953 128 192) (uvalueMInt (extract v_7955 128 192))) 0 64) (extract (shl (extract v_7953 192 256) (uvalueMInt (extract v_7955 192 256))) 0 64))));
      pure ()
    pat_end;
    pattern fun (v_3147 : Mem) (v_3148 : reg (bv 128)) (v_3149 : reg (bv 128)) => do
      v_14313 <- getRegister v_3148;
      v_14315 <- evaluateAddress v_3147;
      v_14316 <- load v_14315 16;
      setRegister (lhs.of_reg v_3149) (concat (extract (shl (extract v_14313 0 64) (uvalueMInt (extract v_14316 0 64))) 0 64) (extract (shl (extract v_14313 64 128) (uvalueMInt (extract v_14316 64 128))) 0 64));
      pure ()
    pat_end;
    pattern fun (v_3158 : Mem) (v_3160 : reg (bv 256)) (v_3161 : reg (bv 256)) => do
      v_14328 <- getRegister v_3160;
      v_14330 <- evaluateAddress v_3158;
      v_14331 <- load v_14330 32;
      setRegister (lhs.of_reg v_3161) (concat (extract (shl (extract v_14328 0 64) (uvalueMInt (extract v_14331 0 64))) 0 64) (concat (extract (shl (extract v_14328 64 128) (uvalueMInt (extract v_14331 64 128))) 0 64) (concat (extract (shl (extract v_14328 128 192) (uvalueMInt (extract v_14331 128 192))) 0 64) (extract (shl (extract v_14328 192 256) (uvalueMInt (extract v_14331 192 256))) 0 64))));
      pure ()
    pat_end
