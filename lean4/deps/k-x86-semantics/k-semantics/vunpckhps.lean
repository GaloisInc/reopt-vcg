def vunpckhps1 : instruction :=
  definst "vunpckhps" $ do
    pattern fun (v_2503 : reg (bv 128)) (v_2504 : reg (bv 128)) (v_2505 : reg (bv 128)) => do
      v_3707 <- getRegister v_2503;
      v_3709 <- getRegister v_2504;
      setRegister (lhs.of_reg v_2505) (concat (concat (concat (extract v_3707 0 32) (extract v_3709 0 32)) (extract v_3707 32 64)) (extract v_3709 32 64));
      pure ()
    pat_end;
    pattern fun (v_2515 : reg (bv 256)) (v_2516 : reg (bv 256)) (v_2517 : reg (bv 256)) => do
      v_3722 <- getRegister v_2515;
      v_3724 <- getRegister v_2516;
      setRegister (lhs.of_reg v_2517) (concat (concat (concat (concat (extract v_3722 0 32) (extract v_3724 0 32)) (extract v_3722 32 64)) (extract v_3724 32 64)) (concat (concat (concat (extract v_3722 128 160) (extract v_3724 128 160)) (extract v_3722 160 192)) (extract v_3724 160 192)));
      pure ()
    pat_end;
    pattern fun (v_2498 : Mem) (v_2499 : reg (bv 128)) (v_2500 : reg (bv 128)) => do
      v_6950 <- evaluateAddress v_2498;
      v_6951 <- load v_6950 16;
      v_6953 <- getRegister v_2499;
      setRegister (lhs.of_reg v_2500) (concat (concat (concat (extract v_6951 0 32) (extract v_6953 0 32)) (extract v_6951 32 64)) (extract v_6953 32 64));
      pure ()
    pat_end;
    pattern fun (v_2509 : Mem) (v_2510 : reg (bv 256)) (v_2511 : reg (bv 256)) => do
      v_6961 <- evaluateAddress v_2509;
      v_6962 <- load v_6961 32;
      v_6964 <- getRegister v_2510;
      setRegister (lhs.of_reg v_2511) (concat (concat (concat (concat (extract v_6962 0 32) (extract v_6964 0 32)) (extract v_6962 32 64)) (extract v_6964 32 64)) (concat (concat (concat (extract v_6962 128 160) (extract v_6964 128 160)) (extract v_6962 160 192)) (extract v_6964 160 192)));
      pure ()
    pat_end
