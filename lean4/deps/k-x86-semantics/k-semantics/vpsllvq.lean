def vpsllvq1 : instruction :=
  definst "vpsllvq" $ do
    pattern fun (v_3233 : reg (bv 128)) (v_3234 : reg (bv 128)) (v_3235 : reg (bv 128)) => do
      v_7988 <- getRegister v_3234;
      v_7990 <- getRegister v_3233;
      setRegister (lhs.of_reg v_3235) (concat (extract (shl (extract v_7988 0 64) (extract v_7990 0 64)) 0 64) (extract (shl (extract v_7988 64 128) (extract v_7990 64 128)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_3244 : reg (bv 256)) (v_3245 : reg (bv 256)) (v_3246 : reg (bv 256)) => do
      v_8005 <- getRegister v_3245;
      v_8007 <- getRegister v_3244;
      setRegister (lhs.of_reg v_3246) (concat (extract (shl (extract v_8005 0 64) (extract v_8007 0 64)) 0 64) (concat (extract (shl (extract v_8005 64 128) (extract v_8007 64 128)) 0 64) (concat (extract (shl (extract v_8005 128 192) (extract v_8007 128 192)) 0 64) (extract (shl (extract v_8005 192 256) (extract v_8007 192 256)) 0 64))));
      pure ()
    pat_end;
    pattern fun (v_3227 : Mem) (v_3228 : reg (bv 128)) (v_3229 : reg (bv 128)) => do
      v_14119 <- getRegister v_3228;
      v_14121 <- evaluateAddress v_3227;
      v_14122 <- load v_14121 16;
      setRegister (lhs.of_reg v_3229) (concat (extract (shl (extract v_14119 0 64) (extract v_14122 0 64)) 0 64) (extract (shl (extract v_14119 64 128) (extract v_14122 64 128)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_3238 : Mem) (v_3239 : reg (bv 256)) (v_3240 : reg (bv 256)) => do
      v_14132 <- getRegister v_3239;
      v_14134 <- evaluateAddress v_3238;
      v_14135 <- load v_14134 32;
      setRegister (lhs.of_reg v_3240) (concat (extract (shl (extract v_14132 0 64) (extract v_14135 0 64)) 0 64) (concat (extract (shl (extract v_14132 64 128) (extract v_14135 64 128)) 0 64) (concat (extract (shl (extract v_14132 128 192) (extract v_14135 128 192)) 0 64) (extract (shl (extract v_14132 192 256) (extract v_14135 192 256)) 0 64))));
      pure ()
    pat_end
