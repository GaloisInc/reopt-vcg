def vunpcklps1 : instruction :=
  definst "vunpcklps" $ do
    pattern fun (v_3266 : reg (bv 128)) (v_3267 : reg (bv 128)) (v_3268 : reg (bv 128)) => do
      v_7606 <- getRegister v_3266;
      v_7608 <- getRegister v_3267;
      setRegister (lhs.of_reg v_3268) (concat (concat (concat (extract v_7606 64 96) (extract v_7608 64 96)) (extract v_7606 96 128)) (extract v_7608 96 128));
      pure ()
    pat_end;
    pattern fun (v_3277 : reg (bv 256)) (v_3278 : reg (bv 256)) (v_3279 : reg (bv 256)) => do
      v_7621 <- getRegister v_3277;
      v_7623 <- getRegister v_3278;
      setRegister (lhs.of_reg v_3279) (concat (concat (concat (concat (extract v_7621 64 96) (extract v_7623 64 96)) (extract v_7621 96 128)) (extract v_7623 96 128)) (concat (concat (concat (extract v_7621 192 224) (extract v_7623 192 224)) (extract v_7621 224 256)) (extract v_7623 224 256)));
      pure ()
    pat_end;
    pattern fun (v_3260 : Mem) (v_3261 : reg (bv 128)) (v_3262 : reg (bv 128)) => do
      v_13462 <- evaluateAddress v_3260;
      v_13463 <- load v_13462 16;
      v_13465 <- getRegister v_3261;
      setRegister (lhs.of_reg v_3262) (concat (concat (concat (extract v_13463 64 96) (extract v_13465 64 96)) (extract v_13463 96 128)) (extract v_13465 96 128));
      pure ()
    pat_end;
    pattern fun (v_3271 : Mem) (v_3272 : reg (bv 256)) (v_3273 : reg (bv 256)) => do
      v_13473 <- evaluateAddress v_3271;
      v_13474 <- load v_13473 32;
      v_13476 <- getRegister v_3272;
      setRegister (lhs.of_reg v_3273) (concat (concat (concat (concat (extract v_13474 64 96) (extract v_13476 64 96)) (extract v_13474 96 128)) (extract v_13476 96 128)) (concat (concat (concat (extract v_13474 192 224) (extract v_13476 192 224)) (extract v_13474 224 256)) (extract v_13476 224 256)));
      pure ()
    pat_end
