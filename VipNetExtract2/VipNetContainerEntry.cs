using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using Org.BouncyCastle.Asn1;
using Org.BouncyCastle.Asn1.CryptoPro;
using Org.BouncyCastle.Asn1.X509;
using Org.BouncyCastle.Asn1.Pkcs;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Digests;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Macs;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.Security;
using Org.BouncyCastle.Utilities.Encoders;

namespace VipNetExtract
{
    class VipNetContainerEntry
    {
        public VipNetContainerEntry(Asn1Sequence seq, byte[] keyBlock)
        {
            Version = (DerInteger)seq[0];
            KeyInfo = VipNetKeyInfo.GetInstance(seq[1]);
            DefenceKeyInfo = VipNetKeyInfo.GetInstance(seq[2]);
            KeyBlock = keyBlock;

            for (int i = 3; i < seq.Count; ++i) {
                if (seq[i] is Asn1TaggedObject tag) {
                    switch (tag.TagNo) {
                        case 0:
                            Certificate = X509CertificateStructure.GetInstance(tag.GetObject());
                            break;
                        case 1:
                            PublicKey = (DerOctetString)tag.GetObject();
                            break;
                    }
                }
            }
        }

        public DerInteger Version { get; }
        public VipNetKeyInfo KeyInfo { get; }
        public VipNetKeyInfo DefenceKeyInfo { get; }
        public X509CertificateStructure Certificate { get; }
        public DerOctetString PublicKey { get; internal set; }
        public byte[] KeyBlock { get; }

        public byte[] GetProtectionKey(string pin)
        {
            if (KeyInfo.KeyClass.Value.IntValue != 64 && KeyInfo.KeyType.Value.IntValue != 24622)
                throw new CryptographicException("Вспомогательный контейнер не содержит ключа защиты");
            var cek = KeyBlock.Take(KeyBlock.Length - 12).ToArray();
            var mac = KeyBlock.Skip(cek.Length).Take(4).ToArray();
            var data = cek.Concat(KeyInfo.RawData).ToArray();
            var pinKey = GetDecryptionKey(pin, null);

            CheckMac(pinKey, cek, data, mac);

            var iv = KeyBlock.Skip(KeyBlock.Length - 8).ToArray();
            return DecryptKey(pinKey, cek, iv);
        }

        public BigInteger GetPrivateKey(string pin, VipNetContainer defence)
        {
            var cek = KeyBlock.Take(KeyBlock.Length - 12).ToArray();
            var mac = KeyBlock.Skip(cek.Length).Take(4).ToArray();
            var data = cek.Concat(KeyInfo.RawData).ToArray();
            var pinKey = GetDecryptionKey(pin, defence);

            CheckMac(pinKey, cek, data, mac);

            var iv = KeyBlock.Skip(KeyBlock.Length - 8).ToArray();
            var pkeyMasked = DecryptKey(pinKey, cek, iv);

            byte[] privateKey;
            if (KeyInfo.KeyClass.Value.And(BigInteger.Three).Equals(BigInteger.Zero)) {
                data = pkeyMasked.Take(pkeyMasked.Length / 2).ToArray();
                var unwrappingKey = pkeyMasked.Skip(pkeyMasked.Length / 2).ToArray();
                privateKey = DecryptKey(unwrappingKey, data);
            } else {
                var wrapped = pkeyMasked.Take(pkeyMasked.Length / 2).Reverse().ToArray();
                var mask = pkeyMasked.Skip(pkeyMasked.Length / 2).Reverse().ToArray();

                var algParams = Gost3410PublicKeyAlgParameters.GetInstance(KeyInfo.Algorithm.Parameters);
                var param = new ECKeyGenerationParameters(algParams.PublicKeyParamSet, new SecureRandom());

                var x = new BigInteger(1, wrapped);
                var y = new BigInteger(1, mask);
                var z = x.Multiply(y).Mod(param.DomainParameters.Curve.Order);

                CheckPrivateKey(param, z);

                privateKey = z.ToByteArrayUnsigned();
            }

            return new BigInteger(1, privateKey);
        }

        private byte[] PBKDF2(IMac hmac, byte[] password, byte[] salt, int iterations, int keyLength)
        {
            // HMAC(HASH, key, msg) = HASH((key ^ 0x5c...) + HASH((key ^ 0x36...) + msg))
            // U(HASH, key, salt, blockNum_be_int32, 1) = HMAC(HASH, key, salt + blockNum_be_int32)
            // U(..., N) = HMAC(HASH, key, U(..., N-1))
            // F(..., N) = U(..., 1) ^ ... ^ U(..., N)
            // PBKDF2(HASH, password, salt, N, keyLength, blockSize) =
            //     (F(HASH, password, salt, 1, N) + ... +
            //     F(HASH, password, salt, ceil(keyLength / blockSize), N)).resize(keyLength)
            int blockSize = hmac.GetMacSize();
            hmac.Init(new KeyParameter(password));
            int numBlocks = (keyLength+blockSize-1)/blockSize;
            var output = new byte[numBlocks*blockSize];
            var blockNumBuf = new byte[4];
            for (int blockNum = 1; blockNum <= numBlocks; blockNum++)
            {
                blockNumBuf[0] = (byte)(blockNum >> 24);
                blockNumBuf[1] = (byte)(blockNum >> 16);
                blockNumBuf[2] = (byte)(blockNum >> 8);
                blockNumBuf[3] = (byte)(blockNum);
                byte[] block = new byte[blockSize];
                byte[] F = new byte[blockSize];
                hmac.BlockUpdate(salt, 0, salt.Length);
                hmac.BlockUpdate(blockNumBuf, 0, 4);
                hmac.DoFinal(F, 0);
                hmac.Reset();
                for (int j = 0; j < F.Length; j++)
                    block[j] = F[j];
                for (int iter = 1; iter < iterations; iter++)
                {
                    hmac.BlockUpdate(F, 0, F.Length);
                    hmac.DoFinal(F, 0);
                    hmac.Reset();
                    for (int j = 0; j < F.Length; j++)
                        block[j] = (byte)(block[j] ^ F[j]);
                }
                for (int j = 0; j < block.Length; j++)
                    output[(blockNum-1)*blockSize + j] = block[j];
            }
            Array.Resize(ref output, keyLength);
            return output;
        }

        private byte[] GetDecryptionKey(string pin, VipNetContainer defence)
        {
            var passwordData = Encoding.ASCII.GetBytes(pin ?? "");
            if (DefenceKeyInfo.KeyClass.Value.IntValue == 64 && DefenceKeyInfo.KeyType.Value.IntValue == 24622)
            {
                // Контейнер зашифрован ключом, лежащим в ещё одном контейнере
                if (defence == null)
                    throw new CryptographicException("Закрытый ключ зашифрован секретным ключом, расположенным в отдельном вспомогательном контейнере. Используйте опцию --defence");
                return defence.Entries[0].GetProtectionKey(pin);
            }
            if (DefenceKeyInfo.Algorithm != null &&
                DefenceKeyInfo.Algorithm.Algorithm.Equals(PkcsObjectIdentifiers.IdPbkdf2))
            {
                // PBKDF2 используется в контейнерах ViPNet Jcrypto SDK
                // Самое смешное, что сам десктопный ViPNet CSP не понимает такие контейнеры
                // А мы понимаем!
                var p = Pbkdf2Params.GetInstance(DefenceKeyInfo.Algorithm.Parameters);
                return PBKDF2(
                    MacUtilities.GetMac(p.Prf.Algorithm),
                    passwordData,
                    p.GetSalt(),
                    p.IterationCount.IntValue,
                    p.KeyLength.IntValue
                );
            }
            var digest = new Gost3411Digest();
            var keyData = new byte[digest.GetDigestSize()];
            var unwrappingKey = new byte[digest.GetDigestSize()];

            digest.BlockUpdate(passwordData, 0, passwordData.Length);
            digest.DoFinal(keyData, 0);
            digest.Reset();

            var secodeData = passwordData.Concat(keyData).ToArray();
            digest.BlockUpdate(secodeData, 0, secodeData.Length);
            digest.DoFinal(unwrappingKey, 0);

            var tmp = new int[keyData.Length / 4];
            for (int i = 0; i < keyData.Length; i += 4)
                tmp[i / 4] = BitConverter.ToInt32(keyData, i) - BitConverter.ToInt32(unwrappingKey, i);

            return tmp.SelectMany(x => BitConverter.GetBytes(x)).ToArray();
        }

        private static void CheckMac(byte[] key, byte[] cek, byte[] data, byte[] mac)
        {
            var m = new Gost28147Mac();
            var keyPrm = ParameterUtilities.CreateKeyParameter("GOST", key);
            m.Init(keyPrm);

            var cekmac = new byte[4];
            m.BlockUpdate(data, 0, data.Length);
            m.DoFinal(cekmac, 0);

            if (!mac.SequenceEqual(cekmac))
                throw new CryptographicException("Неверный ПИН-код");
        }

        private static byte[] DecryptKey(byte[] key, byte[] cek, byte[] iv = null)
        {
            var cipher = CipherUtilities.GetCipher("GOST/CFB/NOPADDING");
            ICipherParameters prms = ParameterUtilities.CreateKeyParameter("GOST", key);
            prms = new ParametersWithSBox(prms, Gost28147Engine.GetSBox("E-A"));
            cipher.Init(false, iv == null ? prms : new ParametersWithIV(prms, iv));
            return cipher.ProcessBytes(cek);
        }

        private void CheckPrivateKey(ECKeyGenerationParameters param, BigInteger privateKey)
        {
            var point = param.DomainParameters.G.Multiply(privateKey).Normalize();
            var x = point.AffineXCoord.GetEncoded().Reverse();
            var y = point.AffineYCoord.GetEncoded().Reverse();
            var pub = PublicKey.GetOctets();

            if (!x.SequenceEqual(pub.Take(pub.Length / 2)) || !y.SequenceEqual(pub.Skip(pub.Length / 2)))
                throw new CryptographicException("Закрытый ключ не соответствует открытому ключу.");
        }
    }
}
